/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class InlinedCallAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private final List<CallStatement> mCallStatements;
	private final boolean mIsReturn;
	private final boolean mIsCallAndReturn;

	public InlinedCallAnnotation(final CallStatement callStmt, final boolean isReturn) {
		mCallStatements = Collections.singletonList(callStmt);
		mIsReturn = isReturn;
		mIsCallAndReturn = false;
	}

	private InlinedCallAnnotation(final List<CallStatement> calls, final boolean isReturn,
			final boolean isCallAndReturn) {
		mCallStatements = calls;
		mIsReturn = isReturn;
		mIsCallAndReturn = isCallAndReturn;
	}

	public CallStatement getCallStatement() {
		if (mCallStatements.size() > 1) {
			throw new UnsupportedOperationException(
					"You should not try to infer an inlined call from a merged annotation");
		}
		return mCallStatements.get(0);
	}

	public boolean isReturn() {
		if (mIsCallAndReturn) {
			throw new UnsupportedOperationException(
					"You should not try to infer an inlined call from a merged annotation");
		}
		return mIsReturn;
	}

	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(InlinedCallAnnotation.class.getName(), this);
	}

	public static InlinedCallAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, InlinedCallAnnotation.class.getName(), a -> (InlinedCallAnnotation) a);
	}

	@Override
	public String toString() {
		return String.valueOf(mCallStatements);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof InlinedCallAnnotation) {
			final InlinedCallAnnotation otherAnnot = ((InlinedCallAnnotation) other);
			final List<CallStatement> callStmts = new ArrayList<>();
			callStmts.addAll(mCallStatements);
			callStmts.addAll(otherAnnot.mCallStatements);
			return new InlinedCallAnnotation(callStmts, otherAnnot.mIsReturn && mIsReturn,
					mIsCallAndReturn || otherAnnot.mIsCallAndReturn || (mIsReturn != otherAnnot.mIsReturn));
		}
		return super.merge(other);
	}
}