import { ApiPromise, WsProvider } from '@polkadot/api';
import { SubmittableExtrinsic } from '@polkadot/api/types';
import { parse } from 'ts-command-line-args';

interface Args {
    network: string,
    addrTo: string,
    amount: bigint,
    forceFrom?: string,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        network: { type: String, description: 'WebSocket endpoint to connect to' },
        addrTo: { type: String, description: 'The address of the beneficiary account' },
        forceFrom: { type: String, optional: true, description: 'Force transfer from the specified account' },
        amount: { type: BigInt, description: 'Amount to transfer' },
        help: { type: Boolean, optional: true, description: 'Print the help message' },
    }, { helpArg: 'help' });

    const api = await ApiPromise.create({ provider: new WsProvider(args.network) });

    let call: SubmittableExtrinsic<'promise'>;
    if (!args.forceFrom) {
        call = api.tx.balances.transferKeepAlive(args.addrTo, args.amount);
    } else {
        call = api.tx.balances.forceTransfer(args.forceFrom, args.addrTo, args.amount)
    }

    console.log(call.method.toHex());
    await api.disconnect();
})();
