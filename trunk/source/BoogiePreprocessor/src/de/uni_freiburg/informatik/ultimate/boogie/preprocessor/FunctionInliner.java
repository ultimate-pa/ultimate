/*
 * Copyright (C) 2009-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Sergio Feo Arenis (arenis@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.CachingBoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;

/**
 * This class removes function bodies by either inlining them (if the attribute "inline" is set) or by adding a
 * corresponding axiom stating that for all input values the function returns the output given by the body.
 *
 * @author hoenicke
 */
public class FunctionInliner extends CachingBoogieTransformer implements IUnmanagedObserver {

	/**
	 * A map containing the functions that should be inlined. The key is the function name.
	 */
	private Map<String, FunctionDeclaration> mInlinedFunctions;
	/**
	 * The current scope containing the renamings and names used.
	 */
	private Scope mCurrentScope;

	@Override
	/**
	 * Process a boogie file. This is called by the tree walker and processes the main node of the tree that starts the
	 * Boogie AST.
	 */
	public boolean process(final IElement root) {
		// Check if node is the first node of the AST.
		if (!(root instanceof Unit)) {
			return true;
		}
		final Unit unit = (Unit) root;
		final List<Declaration> newDeclarations = new ArrayList<>();
		mInlinedFunctions = new HashMap<>();

		// Process all declarations, copying them and replacing function
		// declarations (removing inlined functions, removing bodies of
		// other functions and adding axioms).
		// It also collects inlined function in the hash map
		// inlinedFunctions.
		for (final Declaration decl : unit.getDeclarations()) {
			if (decl instanceof FunctionDeclaration) {
				final FunctionDeclaration fdecl = (FunctionDeclaration) decl;
				if (fdecl.getBody() == null) {
					newDeclarations.add(fdecl);
					continue;
				}
				if (hasFunctionInlineAttr(fdecl)) {
					continue;
				}

				final List<Expression> params = new ArrayList<>();
				int anonctr = 0;
				for (final VarList vl : fdecl.getInParams()) {
					if (vl.getIdentifiers().length == 0) {
						params.add(new IdentifierExpression(vl.getLocation(), vl.getType().getBoogieType(),
								"#" + anonctr++, new DeclarationInformation(StorageClass.QUANTIFIED, null)));
					} else {
						for (final String i : vl.getIdentifiers()) {
							params.add(new IdentifierExpression(vl.getLocation(), vl.getType().getBoogieType(), i,
									new DeclarationInformation(StorageClass.QUANTIFIED, null)));
						}
					}
				}
				final Expression[] funcParams = params.toArray(new Expression[params.size()]);
				final Expression funcApp = new FunctionApplication(fdecl.getLocation(),
						fdecl.getOutParam().getType().getBoogieType(), fdecl.getIdentifier(), funcParams);
				final Trigger funcTrigger = new Trigger(fdecl.getLocation(), new Expression[] { funcApp });
				final Expression funcEq = new BinaryExpression(fdecl.getLocation(), BoogieType.TYPE_BOOL,
						BinaryExpression.Operator.COMPEQ, funcApp, fdecl.getBody());
				final Expression funcDecl = new QuantifierExpression(fdecl.getLocation(), BoogieType.TYPE_BOOL, true,
						fdecl.getTypeParams(), fdecl.getInParams(), new Attribute[] { funcTrigger }, funcEq);
				final Axiom fdeclAxiom = new Axiom(fdecl.getLocation(), new Attribute[0], funcDecl);
				newDeclarations.add(new FunctionDeclaration(fdecl.getLocation(), fdecl.getAttributes(),
						fdecl.getIdentifier(), fdecl.getTypeParams(), fdecl.getInParams(), fdecl.getOutParam()));
				newDeclarations.add(fdeclAxiom);
			} else {
				newDeclarations.add(decl);
			}
		}
		// create the outer scope.
		mCurrentScope = new Scope();
		// process all declarations, which does the inlining.
		for (int i = 0; i < newDeclarations.size(); i++) {
			newDeclarations.set(i, processDeclaration(newDeclarations.get(i)));
		}
		mCurrentScope = null;
		mInlinedFunctions = null;
		unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
		return false;
	}

	private boolean hasFunctionInlineAttr(final FunctionDeclaration fdecl) {
		for (final Attribute attr : fdecl.getAttributes()) {
			if (attr instanceof NamedAttribute) {
				final NamedAttribute nattr = (NamedAttribute) attr;
				final Expression[] val = nattr.getValues();
				if (!"inline".equals(nattr.getName())) {
					continue;
				}
				if (val.length != 1 || !(val[0] instanceof BooleanLiteral)) {
					throw new RuntimeException("inline attribute with wrong parameters: "
							+ Arrays.stream(val).map(BoogiePrettyPrinter::print).collect(Collectors.joining(", "))
							+ " (should be only 1 and of type bool)");
				}
				if (((BooleanLiteral) val[0]).getValue()) {
					mInlinedFunctions.put(fdecl.getIdentifier(), fdecl);
					return true;
				}
				return false;
			}
		}
		return false;
	}

	@Override
	/**
	 * Process a declaration. This creates new scopes for function and procedures, that store input and output
	 * variables.
	 */
	protected Declaration processDeclaration(final Declaration d) {
		if (d instanceof FunctionDeclaration || d instanceof Procedure) {
			mCurrentScope = new Scope(mCurrentScope);
			final Declaration result = super.processDeclaration(d);
			mCurrentScope = mCurrentScope.getParent();
			return result;
		}
		return super.processDeclaration(d);
	}

	@Override
	/**
	 * Process a body. This creates new scope for storing local variables.
	 */
	protected Body processBody(final Body b) {
		mCurrentScope = new Scope(mCurrentScope);
		final Body result = super.processBody(b);
		mCurrentScope = mCurrentScope.getParent();
		return result;
	}

	@Override
	/**
	 * Process a variable declaration list. This adds all variables to the name clash set of the current scope.
	 */
	public VarList processVarList(final VarList vl) {
		for (final String name : vl.getIdentifiers()) {
			mCurrentScope.declareName(name);
		}
		return super.processVarList(vl);
	}

	@Override
	/**
	 * Process an expression. This replaces identifiers according to the renaming (if present), inlines function calls,
	 * and renames identifiers in quantifiers in case a name from an inlined function clashes with a name declared in
	 * the outer scope.
	 */
	public Expression processExpression(final Expression expr) {
		Expression newExpr = null;
		if (expr instanceof IdentifierExpression) {
			// rename identifiers according to the renaming map in the scope.
			final String name = ((IdentifierExpression) expr).getIdentifier();
			final Expression renamed = mCurrentScope.lookupRenaming(name);
			if (renamed != null) {
				newExpr = renamed;
			}
		} else if (expr instanceof FunctionApplication) {
			// inline function applications
			final FunctionApplication app = (FunctionApplication) expr;
			final String name = app.getIdentifier();
			if (mInlinedFunctions.containsKey(name)) {
				mCurrentScope = new Scope(mCurrentScope);
				final FunctionDeclaration fdecl = mInlinedFunctions.get(name);
				final Expression[] args = app.getArguments();
				int pnr = 0;
				for (final VarList vl : fdecl.getInParams()) {
					if (vl.getIdentifiers().length == 0) {
						pnr++;
					} else {
						for (final String i : vl.getIdentifiers()) {
							mCurrentScope.addRenaming(i, processExpression(args[pnr++]));
						}
					}
				}
				final Expression newBody = processExpression(fdecl.getBody());
				mCurrentScope = mCurrentScope.getParent();
				newExpr = newBody;
			}
		} else if (expr instanceof QuantifierExpression) {
			// check that quantified variables are unique
			final QuantifierExpression qexpr = (QuantifierExpression) expr;
			mCurrentScope = new Scope(mCurrentScope);
			final VarList[] vl = qexpr.getParameters();
			VarList[] newVl = vl;
			for (int vlNr = 0; vlNr < vl.length; vlNr++) {
				final String[] ids = vl[vlNr].getIdentifiers();
				String[] newIds = ids;
				for (int idNr = 0; idNr < ids.length; idNr++) {
					if (mCurrentScope.clashes(ids[idNr])) {
						if (newIds == ids) {
							newIds = ids.clone();
						}
						int ctr = 0;
						String newname;
						do {
							newname = ids[idNr] + "$" + ctr++;
						} while (mCurrentScope.clashes(newname));
						newIds[idNr] = newname;
						mCurrentScope.addRenaming(ids[idNr],
								new IdentifierExpression(vl[vlNr].getLocation(), vl[vlNr].getType().getBoogieType(),
										newname, new DeclarationInformation(StorageClass.QUANTIFIED, null)));
					}
					if (newIds != ids) {
						if (newVl == vl) {
							newVl = vl.clone();
						}
						newVl[vlNr] = new VarList(vl[vlNr].getLocation(), newIds, vl[vlNr].getType());
					}
				}
			}
			newVl = processVarLists(newVl);
			final Expression subform = processExpression(qexpr.getSubformula());
			final Attribute[] attrs = processAttributes(qexpr.getAttributes());
			mCurrentScope = mCurrentScope.getParent();
			if (vl == newVl && subform == qexpr.getSubformula() && attrs == qexpr.getAttributes()) {
				return expr;
			}
			newExpr = new QuantifierExpression(qexpr.getLocation(), qexpr.getType(), qexpr.isUniversal(),
					qexpr.getTypeParams(), newVl, attrs, subform);
		}
		if (newExpr == null) {
			return super.processExpression(expr);
		}
		ModelUtils.copyAnnotations(expr, newExpr);
		return newExpr;
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		// TODO Replace with a decent implementation!
		return false;
	}

	/**
	 * The information for a scope in which renamings may take place.
	 *
	 * @author hoenicke
	 */
	private static final class Scope {
		/**
		 * A renaming is a map from identifier name to expression.
		 */
		private final Map<String, Expression> mRenamings;
		/**
		 * The variable names used in the current scope and which therefore should not be reused in inlined functions.
		 */
		private final Set<String> mDeclaredName;
		/**
		 * The parent scope.
		 */
		private final Scope mParent;

		public Scope() {
			mParent = null;
			mRenamings = new HashMap<>();
			mDeclaredName = new HashSet<>();
		}

		public Scope(final Scope par) {
			mParent = par;
			mRenamings = new HashMap<>(par.mRenamings);
			mDeclaredName = new HashSet<>(par.mDeclaredName);
		}

		public Scope getParent() {
			return mParent;
		}

		public void addRenaming(final String name, final Expression expr) {
			mRenamings.put(name, expr);
		}

		public Expression lookupRenaming(final String name) {
			// we only need to check current scope, since we clone
			// renamings when creating a new scope.
			return mRenamings.get(name);
		}

		public boolean clashes(final String name) {
			// we only need to check current scope, since we clone
			// declaredName when creating a new scope.
			return mDeclaredName.contains(name);
		}

		public void declareName(final String name) {
			mDeclaredName.add(name);
		}
	}
}
