import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';

interface Args {
    network: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const root = await api.query.sudo.key();

    await api.disconnect();

    console.log(root.toHuman());
})();
