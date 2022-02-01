package de.uni_freiburg.informatik.ultimate.automata.statefactory;

public interface IBuchiComplementNcsbSimpleStateFactory<STATE> extends IEmptyStackStateFactory<STATE>, ISinkStateFactory<STATE>{

	STATE buchiComplementNcsbSimple(int id);
	
}
