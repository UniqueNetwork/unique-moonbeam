import { ApiPromise, Keyring, WsProvider } from '@polkadot/api';
import '@polkadot/api-augment';
import { parse } from 'ts-command-line-args';

interface Args {
    network: string,
    accountSeed: string,
    call: string,
    sudo?: boolean,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        accountSeed: { type: String, description: 'The seed of the extrinsic sender account' },
        call: { type: String, description: 'Encoded call to execute' },
        sudo: { type: Boolean, optional: true, description: 'Execute the call via sudo' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });
    const keyring = new Keyring({ type: 'ethereum' });
    const account = keyring.addFromUri(args.accountSeed, undefined, 'ethereum');

    const call = api.createType('Call', args.call);
    const { method, section } = api.registry.findMetaCall(call.callIndex);
    const extrinsic = api.tx[section][method](...call.args);

    let tx;
    if (args.sudo) {
        tx = api.tx.sudo.sudo(extrinsic);
    } else {
        tx = extrinsic;
    }

    const extrinsicHash = await tx.signAndSend(account);
    await watchExtrinsic(api, extrinsicHash.toHex(), !!args.sudo);

    await api.disconnect();
})();

async function delay(ms: number) {
    await new Promise(res => setTimeout(res, ms));
}

function logDispatchError(dispatchError: any) {
    let errorDescription;
    if (dispatchError.isModule) {
        const moduleError = dispatchError.asModule;
        const errorMeta = dispatchError.registry.findMetaError(moduleError);
        errorDescription = `${errorMeta.section}.${errorMeta.method}`;
    } else {
        errorDescription = dispatchError.toHuman();
    }

    console.error('\textrinsic FAILED:', errorDescription);
}

async function watchExtrinsic(api: ApiPromise, extrinsicHash: string, sudo: boolean) {
    console.log(`Watching extrinsic ${extrinsicHash}...`);

    let currentBlock = 0;
    const maxNumberBlocks = 30;
    let lastBlockHash = null;

    while (currentBlock < maxNumberBlocks) {
        let [
            [{ block }, blockRecords],
            pendingExtrinsics,
        ] = await Promise.all([
            api.rpc.chain.getFinalizedHead().then(hash => Promise.all([
                api.rpc.chain.getBlock(hash),
                api.at(hash).then(api => api.query.system.events()),
            ])),

            api.rpc.author.pendingExtrinsics(),
        ]);

        if (lastBlockHash === block.hash.toHex()) {
            await delay(500);
            continue;
        } else {
            lastBlockHash = block.hash.toHex();
        }

        console.log(`Looking at block ${block.hash}`);

        const pendingIndex = pendingExtrinsics.findIndex(e => e.hash.toHex() === extrinsicHash);
        const inBlockIndex = block.extrinsics.findIndex(e => e.hash.toHex() === extrinsicHash);

        if (pendingIndex >= 0) {
            console.log('\tthe extrinsic is pending');
            continue;
        }

        if (inBlockIndex >= 0) {
            console.log('\tthe extrinsic is in block');

            const extrinsicEvents = blockRecords.filter(
                (r: any) => r.phase.isApplyExtrinsic && r.phase.asApplyExtrinsic.eq(inBlockIndex)
            ).map(r => r.event);

            const extrinsicSystemEvents = extrinsicEvents.filter(e => e.section === 'system');

            const failed = extrinsicSystemEvents.find(e => e.method === 'ExtrinsicFailed');
            if (failed) {
                const dispatchError = api.createType('SpRuntimeDispatchError', failed.data[0].toHex());
                logDispatchError(dispatchError);
                return;
            }

            const success = extrinsicSystemEvents.find(e => e.method === 'ExtrinsicSuccess');
            if (success) {
                if (sudo) {
                    console.log('\tsudo OK');
                    console.log('\tchecking the inner extrinsic result...');
                    const sudid = extrinsicEvents.find(e => e.section === 'sudo' && e.method === 'Sudid');

                    const sudoResult = api.createType('Result<Null, SpRuntimeDispatchError>', sudid!.data[0].toHex());

                    if (sudoResult.isErr) {
                        logDispatchError(sudoResult.asErr);
                        return;
                    }
                }

                console.log('\textrinsic OK');
                return;
            }
        }

        ++currentBlock;
    }

    console.log(`the extrinsic has not been seen in ${maxNumberBlocks} blocks, consider it dropped`);
    return;
}
