import { ApiPromise, WsProvider } from '@polkadot/api';
import { SubmittableExtrinsic } from '@polkadot/api/types';
import { parse } from 'ts-command-line-args';
import { requireExactlyOne } from './util';

interface Args {
    network: string,
    addrTo: string,
    amount?: bigint,
    forceFrom?: string,
    all?: boolean,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        addrTo: { type: String, description: 'The address of the beneficiary account' },
        forceFrom: { type: String, optional: true, description: 'Force transfer from the specified account (optional, conflicts with --all)' },
        amount: { type: BigInt, optional: true, description: 'Amount to transfer (conflicts with --all)' },
        all: { type: Boolean, optional: true, description: 'Transfer all (conflicts with --amount and --forceFrom)' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    requireExactlyOne(args, ['all', 'amount']);

    if (args.all && args.forceFrom) {
        console.error('--all conflicts with --forceFrom');
        process.exit(-1);
    }

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    let call: SubmittableExtrinsic<'promise'>;
    if (args.all) {
        const keepAlive = true;
        call = api.tx.balances.transferAll(args.addrTo, keepAlive);
    } else if (args.forceFrom) {
        call = api.tx.balances.forceTransfer(args.forceFrom, args.addrTo, args.amount!)
    } else {
        call = api.tx.balances.transferKeepAlive(args.addrTo, args.amount!);
    }

    console.log(call.method.toHex());
    await api.disconnect();
})();
