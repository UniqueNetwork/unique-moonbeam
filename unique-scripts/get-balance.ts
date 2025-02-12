import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';

interface Args {
    network: string,
    accountAddr: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        accountAddr: { type: String, description: 'The address of the account in question' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const accountInfo = await api.query.system.account(args.accountAddr)
        .then(a => a.toJSON() as any);

    if (!accountInfo) {
        console.error('account does not exist');
        process.exit(-1);
    }

    const freeBalance = BigInt(accountInfo.data.free.toString());
    const frozenBalance = BigInt(accountInfo.data.frozen.toString());

    const balance = freeBalance - frozenBalance;

    console.log(balance.toString());

    await api.disconnect();
})();
