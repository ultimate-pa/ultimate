/*
 * Copyright (C) 2026 Manuel Bentele
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE
 * CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE CACSL2BoogieTranslator plug-in,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing
 * parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE CACSL2BoogieTranslator
 * plug-in grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.IInterruptReference;

public abstract class InterruptFunction<T extends IInterruptReference> implements IInterruptFunction<T> {

	private Procedure mProc;

	private T mIntReqRef;

	public InterruptFunction(final T ref) {
		this(null, ref);
	}

	public InterruptFunction(final Procedure proc, final T ref) {
		mProc = proc;
		mIntReqRef = ref;
	}

	@Override
	public T getInterruptReference() {
		return mIntReqRef;
	}

	@Override
	public Procedure getProcedure() {
		return mProc;
	}

	@Override
	public void setProcedure(final Procedure proc) {
		assert Objects.isNull(mProc);
		mProc = proc;
	}

}
