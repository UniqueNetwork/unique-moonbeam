// SPDX-License-Identifier: GPL-3.0-only
pragma solidity ^0.8.20;

import "@openzeppelin@5.1.0/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin@5.1.0/contracts/token/ERC721/extensions/ERC721Pausable.sol";
import "@openzeppelin@5.1.0/contracts/access/Ownable.sol";

contract MyNft is ERC721, ERC721Pausable, Ownable {
    constructor(
        address initialOwner,
        string memory symbol,
        string memory tokenName
    ) ERC721(symbol, tokenName) Ownable(initialOwner) {}

    function pause() public onlyOwner {
        _pause();
    }

    function unpause() public onlyOwner {
        _unpause();
    }

    function mintInto(address to, uint256 tokenId) public onlyOwner {
        _mint(to, tokenId);
    }

    function burnFrom(address from, uint256 tokenId) public onlyOwner {
        address spender = _msgSender();
        address previousOwner = _update(address(0), tokenId, spender);
        if (previousOwner == address(0)) {
            revert ERC721NonexistentToken(tokenId);
        }
        if (previousOwner != from) {
            revert ERC721IncorrectOwner(from, tokenId, previousOwner);
        }
    }

    function exists(uint256 tokenId) public view returns (bool) {
        return _ownerOf(tokenId) != address(0);
    }

    function approve(
        address to,
        uint256 tokenId
    ) public override(ERC721) whenNotPaused {
        address owner = _msgSender();
        _approve(to, tokenId, owner);
    }

    function transfer(address to, uint256 tokenId) public whenNotPaused {
        address spender = _msgSender();
        transferFrom(spender, to, tokenId);
    }

    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) public override(ERC721) whenNotPaused {
        address spender = _msgSender();
        if (to == address(0)) {
            revert ERC721InvalidReceiver(address(0));
        }
        address previousOwner = _update(to, tokenId, spender);
        if (previousOwner != from) {
            revert ERC721IncorrectOwner(from, tokenId, previousOwner);
        }
    }

    function _update(
        address to,
        uint256 tokenId,
        address auth
    ) internal override(ERC721, ERC721Pausable) returns (address) {
        return super._update(to, tokenId, auth);
    }
}
