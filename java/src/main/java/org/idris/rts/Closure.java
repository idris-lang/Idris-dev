package org.idris.rts;

import java.util.concurrent.Callable;

public abstract class Closure implements Callable<Object>, Runnable {
    protected final Object [] context;

    protected Closure(final Object ... context) {
	this.context = context;
    }

    public void run() {
	call();
    }

    public abstract Object call();
}
