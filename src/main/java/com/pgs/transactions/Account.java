package com.pgs.transactions;

class Account {

    private long balance;

    Account() {
        this(0);
    }

    Account(int initialBalance) {
        this.balance = initialBalance;
    }

    long getBalance() {
        return balance;
    }

    void deposit(int amount) {
        balance += amount;
    }

    void withdraw(int amount) {
        balance -= amount;
    }
}
