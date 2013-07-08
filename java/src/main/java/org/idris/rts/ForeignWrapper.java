/*
 */
package org.idris.rts;

public abstract class ForeignWrapper {
    protected abstract Object wrappedInvoke() throws Exception;
    public Object invoke() {
        try {
            return wrappedInvoke();
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
    } 
}
