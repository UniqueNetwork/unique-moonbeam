import { Keyring } from '@polkadot/api';
import { randomAsHex, cryptoWaitReady } from '@polkadot/util-crypto';
import { parse } from 'ts-command-line-args';
import { requireAtLeastOne, requireExactlyOne } from './util';

interface Args {
    byName?: string,
    bySeed?: string,
    new?: boolean,
    showSeed?: boolean,
    showAddr?: boolean,
    help?: boolean;
}

void (async () => {
    const args = parse<Args>({
        byName: {
            type: String,
            optional: true,
            description: 'Get account by name (e.g., alith). Conflicts with --bySeed and --new'
        },
        bySeed: {
            type: String,
            optional: true,
            description: 'Get account by its seed. Conflicts with --byName and --new'
        },
        new: {
            type: Boolean,
            optional: true,
            description: 'Generate new account. Conflicts with --byName and --bySeed'
        },
        showSeed: {
            type: Boolean,
            optional: true,
            description: 'Show the seed of the account. If used with --showAddr, will be printed first'
        },
        showAddr: {
            type: Boolean,
            optional: true,
            description: 'Show the address of the account. If used with --showSeed, will be printed after the seed'
        },
        help: { type: Boolean, optional: true, description: 'Pring the help message' },
    }, { helpArg: 'help' });

    requireExactlyOne(args, ['byName', 'bySeed', 'new']);
    requireAtLeastOne(args, ['showSeed', 'showAddr']);

    let seed: string;
    if (args.byName === 'alith') {
        seed = '0x5fb92d6e98884f76de468fa3f6278f8807c48bebc13595d45af5bdc4da702133';
    } else if (args.byName === 'baltathar') {
        seed = '0x8075991ce870b93a8870eca0c0f91913d12f47948ca0fd25b49c6fa7cdbeee8b';
    } else if (args.byName === 'dorothy') {
        seed = '0x39539ab1876910bbf3a223d84a29e28f1cb4e2e456503e7e91ed39b2e7223d68';
    } else if (args.byName !== undefined) {
        console.error(`unknown account name: ${args.byName}`);
        process.exit(-1);
    }

    if (args.bySeed) {
        seed = args.bySeed;
    }

    if (args.new) {
        seed = randomAsHex(32);
    }

    if (args.showSeed) {
        console.log(seed!);
    }

    if (args.showAddr) {
        await cryptoWaitReady();

        const keyring = new Keyring({ type: 'ethereum' });
        const account = keyring.addFromUri(seed!, undefined, 'ethereum');
        console.log(account.address);
    }
})();
