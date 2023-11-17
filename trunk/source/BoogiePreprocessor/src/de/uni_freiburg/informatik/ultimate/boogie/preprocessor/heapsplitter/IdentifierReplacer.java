/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class IdentifierReplacer extends BoogieTransformer {

	private final String mOldId;
	private final String mNewId;

	public IdentifierReplacer(final String oldId, final String newId) {
		super();
		this.mOldId = oldId;
		this.mNewId = newId;
	}

	@Override
	protected Specification[] processSpecifications(final Specification[] specs) {
		return super.processSpecifications(specs);
	}



//	@Override
//	protected Specification processSpecification(final Specification spec) {
//		if (spec instanceof ModifiesSpecification) {
//			final ModifiesSpecification ms = (ModifiesSpecification) spec;
//			ms.getIdentifiers();
//		}
//		// TODO Auto-generated method stub
//		return super.processSpecification(spec);
//	}



//	@Override
//	protected VarList processVarList(final VarList vl) {
//		final String[] oldIds = vl.getIdentifiers();
//		final String[] newIds = new String[vl.getIdentifiers().length];
//		boolean someModification = false;
//		for (int i = 0; i < vl.getIdentifiers().length; i++) {
//			if (oldIds[i].equals(mOldId)) {
//				someModification = true;
//				newIds[i] = mNewId;
//			} else {
//				newIds[i] = oldIds[i];
//			}
//		}
//		if (someModification) {
//			final VarList result = new VarList(vl.getLoc(), newIds, vl.getType(), vl.getWhereClause());
//			ModelUtils.copyAnnotations(vl, result);
//			return result;
//		} else {
//			return super.processVarList(vl);
//		}
//	}

	@Override
	protected Specification processSpecification(final Specification spec) {
		return super.processSpecification(spec);
	}

	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			final VariableLHS vlhs = (VariableLHS) lhs;
			if (vlhs.getIdentifier().equals(mOldId)) {
				final VariableLHS result = new VariableLHS(lhs.getLoc(), lhs.getType(), mNewId,
						vlhs.getDeclarationInformation());
				ModelUtils.copyAnnotations(lhs, result);
				return result;
			}
		}
		return super.processLeftHandSide(lhs);
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) expr;
			if (ie.getIdentifier().equals(mOldId)) {
				final IdentifierExpression result = new IdentifierExpression(ie.getLoc(), mNewId);
				ModelUtils.copyAnnotations(expr, result);
				return result;
			}
		}
		return super.processExpression(expr);
	}

}
