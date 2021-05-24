package com.pgs.transactions;

class Account {

    //@ spec_public
    private final long limit;

    //@ spec_public
    private long balance;

    /*@
      @ public invariant 0 <= balance;
      @ public invariant balance <= limit;
      @*/

    //@ requires limit >= 0;
    //@ signals_only \nothing;
    //@ pure
    Account(int limit) {
        this(limit, 0);
    }

    //@ requires limit >= 0;
    //@ requires 0 <= initialBalance && initialBalance <= limit;
    //@ signals_only \nothing;
    //@ pure
    Account(int limit, int initialBalance) {
        this.limit = limit;
        this.balance = initialBalance;
    }

    //@ ensures \result == balance;
    //@ pure
    long getBalance() {
        return balance;
    }

    /*@
      @ normal_behavior
      @   assignable balance;
      @   requires amount >= 0;
      @   requires balance + amount <= limit;
      @   ensures balance == \old(balance) + amount;
      @ also exceptional_behavior
      @   assignable \nothing;
      @   requires amount >= 0;
      @   requires balance + amount > limit;
      @   signals (TooMuchMoneyException) \not_modified(balance);
      @   signals_only TooMuchMoneyException;
      @*/
    void deposit(int amount) throws TooMuchMoneyException {
        if (balance > limit - amount) {
            throw new TooMuchMoneyException();
        } else {
            balance += amount;
        }
    }

    /*@
      @ normal_behavior
      @   assignable balance;
      @   requires amount >= 0;
      @   requires balance >= amount;
      @   ensures balance == \old(balance) - amount;
      @ also exceptional_behavior
      @   assignable \nothing;
      @   requires amount >= 0;
      @   requires balance < amount;
      @   signals (NotEnoughMoneyException) \not_modified(balance);
      @   signals_only NotEnoughMoneyException;
      @*/
    void withdraw(int amount) throws NotEnoughMoneyException {
        if (balance < amount) {
            throw new NotEnoughMoneyException();
        } else {
            balance -= amount;
        }
    }
}
