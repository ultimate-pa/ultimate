package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;

public abstract class DoubleDeckerBuilder<LETTER,STATE> extends DoubleDeckerVisitor<LETTER,STATE>{

	Set<STATE> m_SuccessorsConstructedIn = new HashSet<STATE>();
	Set<STATE> m_SuccessorsConstructedCa = new HashSet<STATE>();
//	Set<STATE> m_SuccessorsConstructedRe = new HashSet<STATE>();
	

	
	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE up = doubleDecker.getUp();
		if (m_SuccessorsConstructedIn.contains(up)) {
			HashSet<STATE> succs = new HashSet<STATE>();
			for (LETTER letter : m_TraversedNwa.lettersInternal(up)) {
				for (STATE succ : m_TraversedNwa.succInternal(up, letter)) {
					succs.add(succ);
				}
			}
			return succs;
		}
		else {
			m_SuccessorsConstructedIn.add(up);
			return buildInternalSuccessors(doubleDecker);
		}
	}
	
	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE up = doubleDecker.getUp();
		if (m_SuccessorsConstructedCa.contains(up)) {
			HashSet<STATE> succs = new HashSet<STATE>();
			for (LETTER letter : m_TraversedNwa.lettersCall(up)) {
				for (STATE succ : m_TraversedNwa.succCall(up, letter)) {
					succs.add(succ);
				}
			}
			return succs;
		}
		else {
			m_SuccessorsConstructedCa.add(up);
			return buildCallSuccessors(doubleDecker);
		}
	}



	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
//		STATE up = doubleDecker.getUp();
//		if (m_SuccessorsConstructedRe.contains(up)) {
//			return m_TraversedNwa.succReturn(up);
//		}
//		else {
//			m_SuccessorsConstructedRe.add(up);
			return buildReturnSuccessors(doubleDecker);
//		}
	}
	

	protected abstract Collection<STATE> buildInternalSuccessors(
			DoubleDecker<STATE> doubleDecker);

	protected abstract Collection<STATE> buildCallSuccessors(
			DoubleDecker<STATE> doubleDecker);

	protected abstract Collection<STATE> buildReturnSuccessors(
			DoubleDecker<STATE> doubleDecker);

}
