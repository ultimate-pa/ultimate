package complement;


import automata.IBuchi;
import util.IntSet;

public interface IBuchiComplement extends IBuchi {
	IBuchi getOperand();
	void useOpTransition(int letter, IntSet states);
	int getNumUsedOpTransition();
}
