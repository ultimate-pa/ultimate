/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.boogie.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ISimpleAST;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BoogieASTNode extends BasePayloadContainer implements ISimpleAST<BoogieASTNode, VisualizationNode> {

	private static final long serialVersionUID = 5856434889026482850L;

	// do not rename this field as auto-generated subclasses depend on it
	protected static final Map<Class<?>, Predicate<BoogieASTNode>> VALIDATORS = new HashMap<>();

	private static final String IDENTIFIER_REGEX = "[a-zA-z\\.$#_'`~^\\\\\\?]+[a-zA-z.$#_'~^\\\\\\?\\!\\d]*";

	static {
		final Predicate<BoogieASTNode> iexprValidator = instance -> {
			final IdentifierExpression iexpr = (IdentifierExpression) instance;
			return Pattern.matches(IDENTIFIER_REGEX, iexpr.identifier);
		};
		final Predicate<BoogieASTNode> procIdValidator = instance -> {
			final Procedure proc = (Procedure) instance;
			return Pattern.matches(IDENTIFIER_REGEX, proc.identifier);
		};
		final Predicate<BoogieASTNode> funDeclValidator = instance -> {
			final FunctionDeclaration funDecl = (FunctionDeclaration) instance;
			return Pattern.matches(IDENTIFIER_REGEX, funDecl.identifier);
		};
		final Predicate<BoogieASTNode> funArrayAllNonNullElementsValidator = instance -> {
			final HasNullElementVisitor visitor = new HasNullElementVisitor();
			instance.accept(visitor);
			return !visitor.getResult();
		};

		VALIDATORS.put(IdentifierExpression.class, iexprValidator);
		VALIDATORS.put(Procedure.class, procIdValidator);
		VALIDATORS.put(FunctionDeclaration.class, funDeclValidator);

		VALIDATORS.put(Body.class, funArrayAllNonNullElementsValidator);
		VALIDATORS.put(WhileStatement.class, funArrayAllNonNullElementsValidator);
		VALIDATORS.put(VarList.class, a -> ((VarList) a).getType() != null);
	}

	public BoogieASTNode(final ILocation location) {
		super();
		if (location == null) {
			return;
		}
		location.annotate(this);
	}

	public ILocation getLocation() {
		return ILocation.getAnnotation(this);
	}

	protected BoogieASTNode createSpecialChild(final String name, final Object[] childs) {
		final BoogieASTWrapper parent = new BoogieASTWrapper(null, name);
		for (final Object obj : childs) {
			parent.getOutgoingNodes().add(createSpecialChild(obj));
		}
		return parent;
	}

	protected BoogieASTNode createSpecialChild(final Object obj) {
		return new BoogieASTWrapper(null, obj);
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		return new VisualizationNode(this);
	}

	@Override
	public List<IWalkable> getSuccessors() {
		final ArrayList<IWalkable> rtr = new ArrayList<>();
		for (final BoogieASTNode node : getOutgoingNodes()) {
			rtr.add(node);
		}
		return rtr;
	}

	@Override
	public List<BoogieASTNode> getOutgoingNodes() {
		return new ArrayList<>();
	}

	public void accept(final GeneratedBoogieAstVisitor visitor) {
		throw new UnsupportedOperationException("The base class does not accept visitors");
	}

	public static Check createDefaultCheck(final BoogieASTNode node) {
		if (node instanceof AssertStatement) {
			final NamedAttribute[] attrib = ((AssertStatement) node).getAttributes();
			if (attrib != null && attrib.length > 0) {
				final String namedAttribStr = BoogiePrettyPrinter.print(attrib);
				return new Check(Check.Spec.ASSERT,
						a -> String.format("assertion with attributes \"%s\" always holds", namedAttribStr),
						a -> String.format("assertion with attributes \"%s\" can be violated", namedAttribStr));
			}
			return new Check(Check.Spec.ASSERT);
		} else if (node instanceof LoopInvariantSpecification) {
			return new Check(Check.Spec.INVARIANT);
		} else if (node instanceof CallStatement) {
			return new Check(Check.Spec.PRE_CONDITION);
		} else if (node instanceof EnsuresSpecification) {
			return new Check(Check.Spec.POST_CONDITION);
		} else if (node == null) {
			throw new IllegalArgumentException();
		}
		return null;
	}

	/**
	 * Checks if a {@link BoogieASTNode} type has a array-type field with null elements.
	 *
	 * This class is not complete (it does not check all subtypes of {@link BoogieASTNode} that need checking).
	 *
	 * Note to implementers: Do not descend into children (this class should be used during creation of the AST, and
	 * this would lead to rather long runtimes).
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class HasNullElementVisitor extends GeneratedBoogieAstVisitor {

		private boolean mResult = false;

		@Override
		public boolean visit(final Body node) {
			mResult = hasNullElement(node.getBlock()) || hasNullElement(node.getLocalVars());
			return false;
		}

		@Override
		public boolean visit(final WhileStatement node) {
			mResult = hasNullElement(node.getBody()) || hasNullElement(node.getInvariants());
			return false;
		}

		public boolean getResult() {
			return mResult;
		}

		private static final <T> boolean hasNullElement(final T[] array) {
			if (array == null || array.length == 0) {
				return false;
			}
			return Arrays.stream(array).anyMatch(a -> a == null);
		}
	}

	private class BoogieASTWrapper extends BoogieASTNode {

		private static final long serialVersionUID = 1L;
		private final Object mBacking;

		public BoogieASTWrapper(final ILocation location, final Object backing) {
			super(location);
			mBacking = backing;
		}

		@Override
		public String toString() {
			if (mBacking != null) {
				return mBacking.toString();
			}
			return super.toString();
		}

	}
}
