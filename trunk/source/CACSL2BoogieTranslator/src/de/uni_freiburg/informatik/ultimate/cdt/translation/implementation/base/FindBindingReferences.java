/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IBinding;

/**
 * Searches for references to a given {@link IBinding} in an AST.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class FindBindingReferences extends ASTVisitor {
	private final IBinding mBinding;
	private final Set<IASTName> mReferences = new LinkedHashSet<>();

	/**
	 * Creates a new visitor.
	 *
	 * @param binding
	 *            The binding for which references shall be collected.
	 */
	public FindBindingReferences(final IBinding binding) {
		mBinding = Objects.requireNonNull(binding);
		shouldVisitNames = true;
	}

	public Set<IASTName> getReferences() {
		return Collections.unmodifiableSet(mReferences);
	}

	@Override
	public int visit(final IASTName name) {
		if (name.isReference()) {
			// TODO If resolving the binding is expensive, consider filtering names syntactically
			name.resolveBinding();
			if (mBinding.equals(name.getBinding())) {
				mReferences.add(name);
			}
		}
		return super.visit(name);
	}
}
