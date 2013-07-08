package org.idris.rts;

import java.util.concurrent.Callable;

public abstract class Closure implements Callable<Object>, Runnable {
    protected final Object [] context;

    protected Closure(final Object ... context) {
	this.context = context;
    }

    @Override
    public void run() {
	call();
    }

    @Override
    public abstract Object call();
    
    public Thread fork() {
        Thread childProcess = new Thread(this);
        childProcess.start();
        return childProcess;
    }
}
