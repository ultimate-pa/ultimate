package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public interface IMinimize {

	Object getResult();

	String operationName();

	String startMessage();

	String exitMessage();
}
