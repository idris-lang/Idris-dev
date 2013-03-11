package org.idris.rts;

public class TailCallClosure extends Closure {
    private final Closure function;

    public TailCallClosure(Closure function) {
	super();
	this.function = function;
    }

    public final Object call() {
	Closure function = this.function;
	Object result = null;
	while (function != null) {
	    result = function.call();
	    function = null;
	    if (result instanceof TailCallClosure) {
		function = ((TailCallClosure)result).function;
	    } else {
		return result;
	    }
	}
	return result;
    }
}

