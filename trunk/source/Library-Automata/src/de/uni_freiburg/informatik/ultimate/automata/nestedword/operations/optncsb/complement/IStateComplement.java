package complement;

import automata.IBuchi;
import automata.IState;

public interface IStateComplement extends IState {
	
	IBuchi getOperand();
	
	IBuchi getComplement();
}
