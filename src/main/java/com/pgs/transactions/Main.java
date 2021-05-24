package com.pgs.transactions;

public class Main {
    public static void main(String[] args) {
        Bank bank = new Bank();
        Account source = new Account(100);
        Account destination = new Account(100);

//        System.out.printf("source %d, destination %d\n", source.getBalance(), destination.getBalance());
        bank.transfer(source, destination, 50);
//        System.out.printf("source %d, destination %d\n", source.getBalance(), destination.getBalance());
    }
}
