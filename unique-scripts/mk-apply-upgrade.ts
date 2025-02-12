import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';
import { readFileSync } from 'fs';
import '@polkadot/api-augment';

interface Args {
    network: string,
    file: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        file: { type: String, description: 'A path to a file containing the code' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const data = readFileSync(args.file);
    const hex = api.tx.system.applyAuthorizedUpgrade(data).method.toHex();

    await api.disconnect();

    console.log(hex);
})();
