package operation.intersection;

import automata.IBuchi;

public interface IBuchiIntersection {
	
	IBuchi getFstBuchi();
	IBuchi getSndBuchi();
	
	IBuchi getIntersection();
}
