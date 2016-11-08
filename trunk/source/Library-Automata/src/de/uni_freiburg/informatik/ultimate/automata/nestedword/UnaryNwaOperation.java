/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Abstract operation taking one nested word automaton as input.
 * The most common methods are provided but can also be overwritten.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class UnaryNwaOperation<LETTER, STATE> extends GeneralOperation<LETTER, STATE> {
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	public UnaryNwaOperation(final AutomataLibraryServices services) {
		super(services);
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand " + getOperand().sizeInformation();
	}
	
	/**
	 * @return The operand nested word automaton.
	 */
	protected abstract INestedWordAutomatonSimple<LETTER, STATE> getOperand();
	
	/**
	 * This implementation can be used in the {@link de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 * getResult()} method.
	 * It checks (finite word) language equivalence between the operand and the result.
	 * <p>
	 * NOTE: The operation relies on the {@link de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 * getResult()} method being a constant-time operation.
	 */
	protected Pair<Boolean, String> checkLanguageEquivalence(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// type-check and cast result to nested word automaton
		if (!(getResult() instanceof INestedWordAutomatonSimple)) {
			throw new UnsupportedOperationException(
					"The default checkResult() method assumes the result is a nested word automaton.");
		}
		@SuppressWarnings("unchecked")
		final INestedWordAutomatonSimple<LETTER, STATE> result =
				(INestedWordAutomatonSimple<LETTER, STATE>) getResult();
		final INestedWordAutomatonSimple<LETTER, STATE> operand = getOperand();
		
		// check language equivalence via two inclusion checks
		final String message;
		final Boolean correct;
		if (!new IsIncluded<>(mServices, stateFactory, operand, result).getResult()) {
			message = "The result recognizes less words than before.";
			correct = Boolean.FALSE;
		} else if (!new IsIncluded<>(mServices, stateFactory, result, operand).getResult()) {
			message = "The result recognizes more words than before.";
			correct = Boolean.FALSE;
		} else {
			message = null;
			correct = Boolean.TRUE;
		}
		
		return new Pair<>(correct, message);
	}
}
