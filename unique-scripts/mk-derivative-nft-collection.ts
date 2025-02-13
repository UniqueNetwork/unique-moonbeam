import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';
import '@polkadot/api-augment';

interface Args {
    network: string,
    uniqueCollectionId: number,
    tokenName: string,
    symbol: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        uniqueCollectionId: { type: Number, description: 'The Unique Network NFT collection ID to register on Moonbeam' },
        tokenName: { type: String, description: 'The token name of the derivative collection' },
        symbol: { type: String, description: 'The symbol of the derivative collection' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    const hex = api.tx.derivativeNfts.createDerivative(
        {
            parents: 1,
            interior: {
                X2: [
                    { Parachain: 2037 },
                    { GeneralIndex: args.uniqueCollectionId },
                ],
            },
        },
        {
            symbol: args.symbol,
            tokenName: args.tokenName,
            instanceVariant: 'Index',
        },
    ).method.toHex();

    await api.disconnect();

    console.log(hex);
})();
