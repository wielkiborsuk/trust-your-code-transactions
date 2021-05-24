package com.pgs.transactions;

class Bank {

    //@ requires amount >= 0;
    //@ requires src != dst;
    //@ ensures !\result ==> \not_modified(src.balance) && \not_modified(dst.balance);
    //@ ensures \result ==> src.balance == \old(src.balance) - amount;
    //@ ensures \result ==> dst.balance == \old(dst.balance) + amount;
    boolean transfer(Account src, Account dst, int amount) {
        try {
            src.withdraw(amount);
            dst.deposit(amount);
            return true;
        } catch (NotEnoughMoneyException e) {
            return false;
        } catch (TooMuchMoneyException e) {
            try {
                src.deposit(amount);
            } catch (TooMuchMoneyException ex) {
                return false;
            }
        }
        return false;
    }
}
