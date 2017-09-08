module Public1

import public Public2

public1_private : a -> a
public1_private a = a

export
public1_visible : a -> a
public1_visible = public1_private
