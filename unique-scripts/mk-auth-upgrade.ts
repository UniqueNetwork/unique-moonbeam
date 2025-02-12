import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';
import '@polkadot/api-augment';

interface Args {
    network: string,
    hash: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        hash: { type: String, description: 'Code hash to authorize' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const hex = api.tx.system.authorizeUpgrade(args.hash).method.toHex();

    await api.disconnect();

    console.log(hex);
})();
