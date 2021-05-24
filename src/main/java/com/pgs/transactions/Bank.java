package com.pgs.transactions;

class Bank {

    //@ requires amount >= 0;
    boolean transfer(Account src, Account dst, int amount) {
        try {
            src.withdraw(amount);
            dst.deposit(amount);
            return true;
        } catch (NotEnoughMoneyException | TooMuchMoneyException e) {
            return false;
        }
    }
}
