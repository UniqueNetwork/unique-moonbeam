import { ApiPromise, WsProvider } from '@polkadot/api';
import { readFileSync } from 'fs';
import { parse } from 'ts-command-line-args';

interface Args {
    network: string,
    file: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        file: { type: String, description: 'A path to a file to hash' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const buffer = readFileSync(args.file);
    const hash = api.registry.hash(buffer);

    await api.disconnect();

    console.log(hash.toHex());
})();
