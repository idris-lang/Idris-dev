package org.idris.rts;

import java.util.concurrent.Callable;

public abstract class Closure implements Callable<Object>, Runnable {
    @Override
    public abstract Object call();
    
    public static Object unwrapTailCall(Object o) {
        while (o instanceof Closure) {
            o = ((Closure)o).call();
        }
        return o;
    }
    
    @Override
    public void run() {
	unwrapTailCall(call());
    }
    
    public Thread fork() {
        Thread childProcess = new Thread(this);
        childProcess.start();
        return childProcess;
    }
}
