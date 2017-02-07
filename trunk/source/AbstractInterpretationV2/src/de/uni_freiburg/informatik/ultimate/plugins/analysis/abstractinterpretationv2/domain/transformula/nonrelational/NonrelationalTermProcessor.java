/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Term walker for non-relational abstract domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class NonrelationalTermProcessor extends NonRecursive {
	
	private final ILogger mLogger;
	
	protected NonrelationalTermProcessor(final ILogger logger) {
		mLogger = logger;
	}

	protected void process(final Term term) {
		run(new NonrelationalTermWalker(term, mLogger));
	}
	
	private static class NonrelationalTermWalker extends TermWalker {
		
		private final ILogger mLogger;

		public NonrelationalTermWalker(final Term term, final ILogger logger) {
			super(term);
			mLogger = logger;
		}
		
		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			throw new UnsupportedOperationException();
		}
		
		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			throw new UnsupportedOperationException();
		}
		
		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new NonrelationalTermWalker(t, mLogger));
			}
		}
		
		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			throw new UnsupportedOperationException();
		}
		
		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			throw new UnsupportedOperationException();
		}
		
		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			throw new UnsupportedOperationException();
		}
	}
}
