import {
    Registry,
    parachainUniversalLocation,
    relaychainUniversalLocation,
} from "@ashkuc/simple-xcm";
import {
    asset,
    location,
    nonfungible,
    universalLocation,
} from "@ashkuc/xcm-util/common";

import { ApiPromise, WsProvider } from '@polkadot/api';
import { parse } from 'ts-command-line-args';
import '@polkadot/api-augment';
import { NetworkId } from "@ashkuc/xcm-types";

interface Args {
    moonbeamNetwork: string,
    uniqueNetwork: string,
    uniqueCollectionId: bigint,
    itemIndex: bigint,
    senderAddr: string,
    destAddr: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        moonbeamNetwork: { type: String, description: 'Moonbeam network WS endpoint' },
        uniqueNetwork: { type: String, description: 'Unique network WS endpoint' },
        uniqueCollectionId: { type: BigInt, description: 'The Unique Network NFT collection ID' },
        itemIndex: { type: BigInt, description: 'NFT ID within the collection' },
        senderAddr: { type: String, description: 'The sender account address on Moonbeam to dry run with' },
        destAddr: { type: String, description: 'The beneficiary account on Unique' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const westendNetworkId: NetworkId = {
        byGenesis:
            '0xe143f23803ac50e8f6f8e62695d1ce9e4e1d68aa36c1cd2cfd15340213f3423e',
    };

    const registry = new Registry()
        .addChain({
            identity: {
                name: "Moonbeam",
                universalLocation: parachainUniversalLocation(westendNetworkId, 1000n),
            },
            endpoints: [args.moonbeamNetwork],
        })
        .addCurrency({
            symbol: "GLMR",
            decimals: 18,
            universalLocation: universalLocation(westendNetworkId, [
                { parachain: 2004n },
                { palletInstance: 10n },
            ]),
        })
        .addChain({
            identity: {
                name: "Unique",
                universalLocation: parachainUniversalLocation(westendNetworkId, 2037n),
            },
            endpoints: [args.uniqueNetwork],
        })
        .addUniversalLocation(
            "UniqueNftCollection",
            universalLocation(westendNetworkId, [
                { parachain: 2037n },
                { generalIndex: args.uniqueCollectionId },
            ]),
        )
        .addRelativeLocation(
            "SenderAccount",
            location(0n, [
                {
                    accountKey20: {
                        key: args.senderAddr,
                    },
                },
            ]),
        )
        .addRelativeLocation(
            "DestAccount",
            location(0n, [
                {
                    accountId32: {
                        id: args.destAddr,
                    },
                },
            ]),
        );

    await registry.addNativeCurrency("Unique");

    const xcm = await registry.connectXcm("Moonbeam");

    const transfer = await xcm.composeExtrinsic({
        origin: "SenderAccount",
        assets: [
            asset("UniqueNftCollection", nonfungible(args.itemIndex)),
            xcm.adjustedFungible("UNQ", "20"),
        ],
        feeAssetId: "UNQ",
        destination: "Unique",
        beneficiary: "DestAccount",
    });

    await xcm.disconnect();

    console.log(transfer.submittableExtrinsic.method.toHex());
})();
