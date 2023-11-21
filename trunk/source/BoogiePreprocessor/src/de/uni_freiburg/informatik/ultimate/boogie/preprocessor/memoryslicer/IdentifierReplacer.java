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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class IdentifierReplacer extends BoogieTransformer {

	private final Map<String, String> mOldIdToNewId;
	private final String mOldProcId;
	private final String mSuffix;

	public IdentifierReplacer(final Map<String, String> oldIdToNewId, final String oldProcId, final String suffix) {
		super();
		mOldIdToNewId = oldIdToNewId;
		mOldProcId = oldProcId;
		mSuffix = suffix;
	}

	@Override
	protected Body processBody(final Body body) {
		return super.processBody(body);
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
		final VariableLHS replacement = MemorySliceUtils.replaceLeftHandSide(lhs, mOldIdToNewId, mOldProcId,
				mOldProcId + mSuffix);
		if (replacement != null) {
			return replacement;
		}
		return super.processLeftHandSide(lhs);
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		final IdentifierExpression replacement = MemorySliceUtils.replaceIdentifierExpression(expr, mOldIdToNewId,
				mOldProcId, mOldProcId + mSuffix);
		if (replacement != null) {
			return replacement;
		}
		return super.processExpression(expr);
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		// For C_memcpy we also have to rename `read~unchecked~int` and `write~unchecked~int`
		if (statement instanceof CallStatement) {
			final CallStatement cs = (CallStatement) statement;
			if (cs.getMethodName().startsWith(MemorySliceUtils.READ_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_POINTER)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_POINTER)) {
				assert cs.getArguments().length == 2;
				final VariableLHS[] newLeftHandSides = processVariableLHSs(cs.getLhs());
				final Expression[] newArguments = processExpressions(cs.getArguments());
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						newLeftHandSides, cs.getMethodName() + mSuffix, newArguments);
				ModelUtils.copyAnnotations(statement, result);
				return result;
			} else if (cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_POINTER)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_POINTER)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_POINTER)) {
				assert cs.getArguments().length == 3;
				final VariableLHS[] newLeftHandSides = processVariableLHSs(cs.getLhs());
				final Expression[] newArguments = processExpressions(cs.getArguments());
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						newLeftHandSides, cs.getMethodName() + mSuffix, newArguments);
				ModelUtils.copyAnnotations(statement, result);
				return result;
			}
		}

		return super.processStatement(statement);
	}

}
