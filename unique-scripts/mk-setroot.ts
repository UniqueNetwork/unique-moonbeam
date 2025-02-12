import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';
import '@polkadot/api-augment';

interface Args {
    network: string,
    newSudoAddr: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        newSudoAddr: { type: String, description: 'New sudo account address' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const call = api.tx.sudo.setKey(args.newSudoAddr);

    console.log(call.method.toHex());
    await api.disconnect();
})();
