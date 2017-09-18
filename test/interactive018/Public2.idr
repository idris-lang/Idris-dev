module Public2

public2_private : a -> a
public2_private a = a

export
public2_visible : a -> a
public2_visible = public2_private
