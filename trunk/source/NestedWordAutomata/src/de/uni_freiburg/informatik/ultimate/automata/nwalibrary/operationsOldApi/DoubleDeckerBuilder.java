/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

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
