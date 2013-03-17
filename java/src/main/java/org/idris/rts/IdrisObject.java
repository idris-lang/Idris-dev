package org.idris.rts;

public class IdrisObject {
    private final int constructorId;
    private final Object data[];
    
    public IdrisObject(final int constructorId, final Object ... data) {
	this.constructorId = constructorId;
	this.data = data;
    }
    
    public int getConstructorId() {
	return constructorId;
    }

    public Object[] getData() {
	return data;
    }
}
