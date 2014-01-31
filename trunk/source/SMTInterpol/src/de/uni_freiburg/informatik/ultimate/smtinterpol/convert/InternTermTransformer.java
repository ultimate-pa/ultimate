/*
 * Copyright (C) 2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class InternTermTransformer extends TermTransformer {
	private static class BuildSMTAffineTerm implements Walker {

		private final SMTAffineTerm mOld;
		
		public BuildSMTAffineTerm(SMTAffineTerm old) {
			mOld = old;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			InternTermTransformer transformer = (InternTermTransformer) engine;
			/* collect args and check if they have been changed */
			Term[] oldArgs = mOld.getSummands().keySet().toArray(
					new Term[mOld.getSummands().size()]);
			Term[] newArgs = transformer.getConverted(oldArgs);
			transformer.convertSMTAffineTerm(mOld, newArgs, oldArgs);
		}
		
	}
	
	@Override
	protected void convert(Term term) {
		if (term instanceof SMTAffineTerm) {
			SMTAffineTerm old = (SMTAffineTerm) term;
			enqueueWalker(new BuildSMTAffineTerm(old));
			pushTerms(old.getSummands().keySet().toArray(
					new Term[old.getSummands().size()]));
		} else
			super.convert(term);
	}

	protected void convertSMTAffineTerm(
			SMTAffineTerm old, Term[] newArgs, Term[] oldArgs) {
		SMTAffineTerm res = old;
		if (oldArgs != newArgs) {
			res = SMTAffineTerm.create(old.getConstant(), old.getSort());
			for (int i = 0; i < oldArgs.length; ++i) {
				Rational fac = old.getSummands().get(oldArgs[i]);
				res = res.add(SMTAffineTerm.create(fac, newArgs[i]));
			}
		}
		setResult(res);
	}
	
}
