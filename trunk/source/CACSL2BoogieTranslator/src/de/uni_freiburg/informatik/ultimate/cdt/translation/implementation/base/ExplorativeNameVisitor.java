/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.Arrays;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ILinkage;
import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.DOMException;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.ICompositeType;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IFunctionType;
import org.eclipse.cdt.core.dom.ast.IProblemType;
import org.eclipse.cdt.core.dom.ast.IScope;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.core.dom.ast.IVariable;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Visitor that I use to explore features of CDT.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExplorativeNameVisitor extends ASTVisitor {

	private final ILogger mLogger;

	public ExplorativeNameVisitor(final ILogger logger) {
		// visit all nodes by default
		super(true);
		shouldVisitAmbiguousNodes = true;
		mLogger = logger;
	}

	@Override
	public int visit(final IASTName name) {
		mLogger.info("IASTName");
		mLogger.info("  " + name.getRawSignature());
		final IBinding binding = name.resolveBinding();
		final IASTName[] declarations = name.getTranslationUnit().getDeclarationsInAST(binding);
		Arrays.stream(declarations)
				.forEach(a -> mLogger.info("  " + a.getRawSignature() + " as " + a.getRoleOfName(true)));
		final IScope scope;
		final ILinkage linkage = binding.getLinkage();
		try {
			scope = binding.getScope();
		} catch (final DOMException e) {
			mLogger.fatal("  " + "Exception during getScope: ", e);
			return super.visit(name);
		}

		String scopeName;
		if (scope == null) {
			scopeName = "NOSCOPE";
		} else {
			scopeName = scope.getKind().toString();
		}
		mLogger.info("  " + "Scope: " + scopeName + " Linkage: " + linkage.getLinkageName());

		if (binding instanceof IVariable) {
			final IVariable var = (IVariable) binding;
			mLogger.info("  " + toString(var.getType()));
		} else if (binding instanceof ITypedef) {
			final ITypedef typedef = (ITypedef) binding;
			mLogger.info("  " + toString(typedef.getType()));
		} else if (binding instanceof IFunction) {
			final IFunction function = (IFunction) binding;
			final IScope fScope = function.getFunctionScope();
			if (fScope == null) {
				mLogger.info("  " + "NOFSCOPE");
			} else {
				mLogger.info("  " + fScope.getScopeName());
				mLogger.info("  " + fScope.getKind());
			}

			final IFunctionType fType = function.getType();
			final StringBuilder sb = new StringBuilder();
			sb.append(function.getName());
			sb.append("(");
			sb.append(Arrays.stream(fType.getParameterTypes()).map(this::toString).collect(Collectors.joining(",")));
			sb.append(") :");
			sb.append(toString(fType.getReturnType()));
			mLogger.info("  " + sb.toString() + " " + function.getType().getClass().getSimpleName());
		} else if (binding instanceof ICompositeType) {
			final ICompositeType compType = (ICompositeType) binding;
			mLogger.info("  " + "Fields: " + compType.getFields());
		} else {
			mLogger.info("  " + "Unhandled binding class:" + binding.getClass().getSimpleName());
		}

		return super.visit(name);
	}

	@Override
	public int visit(final IASTStatement statement) {
		mLogger.info(statement.getClass());
		return super.visit(statement);
	}

	private String toString(final IType type) {
		if (type instanceof IProblemType) {
			final IProblemType probType = (IProblemType) type;
			return "Problem: " + probType.getMessage();
		}
		return type + " (" + type.getClass().getSimpleName() + ")";
	}
}