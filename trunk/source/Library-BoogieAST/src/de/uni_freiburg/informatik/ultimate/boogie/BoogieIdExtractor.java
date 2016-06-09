/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;

/**
 * Class that computes all IDs of all IdentifierExpression and all
 * VariableLeftHandSides contained in a given Expression.
 * 
 * @author Matthias Heizmann
 *
 */
public final class BoogieIdExtractor extends BoogieTransformer {

		private final Set<String> mIds = new HashSet<>();

		@Override
		public Expression processExpression(Expression expr) {
			if(expr instanceof IdentifierExpression){
				mIds.add(((IdentifierExpression) expr).getIdentifier());
			}
			return super.processExpression(expr);
		}

		@Override
		protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
			if (lhs instanceof VariableLHS) {
				mIds.add(((VariableLHS) lhs).getIdentifier());
			}
			return super.processLeftHandSide(lhs);
		}

		public Set<String> getIds() {
			return mIds;
		}
	
}

