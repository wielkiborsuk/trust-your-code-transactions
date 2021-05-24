package com.pgs.transactions;

class Bank {

    boolean transfer(Account src, Account dst, int amount) {
        src.withdraw(amount);
        dst.deposit(amount);
        return true;
    }
}
