/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;

public class ConstExpander extends BoogieTransformer implements IUnmanagedObserver {

	private final HashMap<IBoogieType, List<ConstDeclaration>> mConstDecls;
	private final BoogiePreprocessorBacktranslator mBacktranslator;

	protected ConstExpander(BoogiePreprocessorBacktranslator backtranslator) {
		mBacktranslator = backtranslator;
		mConstDecls = new HashMap<IBoogieType, List<ConstDeclaration>>();
	}

	@Override
	public boolean process(IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			final ArrayList<Declaration> newDecls = new ArrayList<Declaration>();
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof ConstDeclaration) {
					final ConstDeclaration constDecl = (ConstDeclaration) decl;
					if (!constDecl.isUnique() && constDecl.getParentInfo() == null) {
						newDecls.add(constDecl);
					} else {
						final VarList vl = constDecl.getVarList();
						addConstDeclaration(vl.getType().getBoogieType(), constDecl);
						final ConstDeclaration newDecl = new ConstDeclaration(constDecl.getLocation(),
								constDecl.getAttributes(), false, vl, null, false);
						newDecls.add(newDecl);
						mBacktranslator.addMapping(constDecl, newDecl);
					}
				} else {
					newDecls.add(decl);
				}
			}

			for (final List<ConstDeclaration> cdlist : mConstDecls.values()) {
				addUniquenessAxioms(newDecls, cdlist);
				addPartOrderAxioms(newDecls, cdlist);
			}
			unit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			return false;
		}
		return true;
	}

	private void addPartOrderAxioms(ArrayList<Declaration> newDecls, List<ConstDeclaration> cdlist) {
		//TODO: PartOrderAxioms are currently not considered for back translation (its unclear how they should be treated) 
		
		final HashMap<String, List<String>> childrens = new HashMap<String, List<String>>();
		final HashMap<String, List<String>> uniqueChildrens = new HashMap<String, List<String>>();
		final HashSet<String> uniqueValues = new HashSet<String>();
		final ASTType asttype = cdlist.get(0).getVarList().getType();
		final IBoogieType type = asttype.getBoogieType();
		final IdentifierExpression var = new IdentifierExpression(asttype.getLocation(), type, "$$",
		/*
		 * FIXME : ask Jochen about storage class
		 */null);
		final IdentifierExpression var2 = new IdentifierExpression(asttype.getLocation(), type, "$$2",
		/*
		 * FIXME : ask Jochen about storage class
		 */null);
		for (final ConstDeclaration c : cdlist) {
			final ParentEdge[] parents = c.getParentInfo();
			for (final String child : c.getVarList().getIdentifiers()) {
				if (c.isUnique()) {
					uniqueValues.add(child);
				}

				if (parents != null) {
					final IdentifierExpression cid = new IdentifierExpression(c.getLocation(), type, child,
					/*
					 * FIXME : ask Jochen about storage class
					 */null);
					Expression polist = null;
					for (final ParentEdge p : parents) {
						final String parent = p.getIdentifier();
						final IdentifierExpression pid = new IdentifierExpression(c.getLocation(), type, parent,
						/*
						 * FIXME : ask Jochen about storage class
						 */null);
						final Expression partorder = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.COMPPO, cid, pid);
						if (polist == null) {
							polist = partorder;
						} else {
							polist = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
									BinaryExpression.Operator.LOGICAND, partorder, polist);
						}
					}
					if (polist != null) {
						newDecls.add(new Axiom(c.getLocation(), new Attribute[0], polist));
					}
					polist = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
							BinaryExpression.Operator.COMPEQ, cid, var);
					for (final ParentEdge p : parents) {
						final String parent = p.getIdentifier();
						final IdentifierExpression pid = new IdentifierExpression(c.getLocation(), type, parent,
						/*
						 * FIXME : ask Jochen about storage class
						 */null);
						List<String> childList = childrens.get(parent);
						if (childList == null) {
							childList = new ArrayList<String>();
							childrens.put(parent, childList);
						}
						childList.add(child);
						if (p.isUnique()) {
							childList = uniqueChildrens.get(parent);
							if (childList == null) {
								childList = new ArrayList<String>();
								uniqueChildrens.put(parent, childList);
							}
							childList.add(child);
						}
						final Expression partorder = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.COMPPO, pid, var);
						polist = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.LOGICOR, partorder, polist);
					}
					final Expression lhs = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
							BinaryExpression.Operator.COMPPO, cid, var);
					final Expression impl = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
							BinaryExpression.Operator.LOGICIMPLIES, lhs, polist);
					final VarList vl = new VarList(c.getLocation(), new String[] { "$$" }, asttype);
					final Trigger trigger = new Trigger(c.getLocation(), new Expression[] { lhs });
					final Expression quant = new QuantifierExpression(c.getLocation(), PrimitiveType.TYPE_BOOL, true,
							new String[0], new VarList[] { vl }, new Attribute[] { trigger }, impl);

					newDecls.add(new Axiom(c.getLocation(), new Attribute[0], quant));
				}
			}
		}

		for (final ConstDeclaration c : cdlist) {
			if (c.isComplete()) {
				for (final String parent : c.getVarList().getIdentifiers()) {
					final IdentifierExpression pid = new IdentifierExpression(c.getLocation(), type, parent,
					/*
					 * FIXME : ask Jochen about storage class
					 */null);
					Expression polist = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
							BinaryExpression.Operator.COMPEQ, var, pid);
					List<String> childList = childrens.get(parent);
					if (childList == null) {
						childList = Collections.emptyList();
					}
					for (final String child : childList) {
						final IdentifierExpression cid = new IdentifierExpression(c.getLocation(), type, child,
						/*
						 * FIXME : ask Jochen about storage class
						 */null);
						final Expression partorder = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.COMPPO, var, cid);
						polist = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.LOGICOR, partorder, polist);
					}
					final Expression lhs = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
							BinaryExpression.Operator.COMPPO, var, pid);
					final Expression impl = new BinaryExpression(c.getLocation(), PrimitiveType.TYPE_BOOL,
							BinaryExpression.Operator.LOGICIMPLIES, lhs, polist);
					final VarList vl = new VarList(c.getLocation(), new String[] { "$$" }, asttype);
					final Trigger trigger = new Trigger(c.getLocation(), new Expression[] { lhs });
					final Expression quant = new QuantifierExpression(c.getLocation(), PrimitiveType.TYPE_BOOL, true,
							new String[0], new VarList[] { vl }, new Attribute[] { trigger }, impl);

					newDecls.add(new Axiom(c.getLocation(), new Attribute[0], quant));
				}
			}
		}

		final Collection<String> uniqueParents = uniqueChildrens.keySet();
		for (final String p1 : uniqueParents) {
			final IdentifierExpression p1id = new IdentifierExpression(null, type, p1,
			/*
			 * FIXME : ask Jochen about storage class
			 */null);
			Collection<String> p2list = uniqueParents;
			if (uniqueValues.contains(p1)) {
				p2list = Collections.singleton(p1);
			}
			for (final String p2 : p2list) {
				if (!uniqueValues.contains(p2) && p1.compareTo(p2) > 0) {
					continue;
				}
				IdentifierExpression p2id;
				Expression pre;
				if (p1.equals(p2)) {
					p2id = p1id;
					pre = null;
				} else {
					p2id = new IdentifierExpression(null, type, p2,
					/*
					 * FIXME: ask Jochen about storage class
					 */null);
					pre = new BinaryExpression(null, PrimitiveType.TYPE_BOOL, BinaryExpression.Operator.COMPEQ, p1id,
							p2id);
				}
				for (final String c1 : uniqueChildrens.get(p1)) {
					final IdentifierExpression c1id = new IdentifierExpression(null, type, c1,
					/*
					 * FIXME : ask Jochen about storage class
					 */null);
					for (final String c2 : uniqueChildrens.get(p2)) {
						if (p1.equals(p2) && c1.compareTo(c2) >= 0 || c1.equals(c2)) {
							continue;
						}
						final IdentifierExpression c2id = new IdentifierExpression(null, type, c2,
						/*
						 * FIXME : ask Jochen about storage class
						 */null);
						Expression pre2 = pre;
						if (!uniqueValues.contains(c1) || !uniqueValues.contains(c2)) {
							final Expression neq = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
									BinaryExpression.Operator.COMPNEQ, c1id, c2id);
							if (pre == null) {
								pre2 = neq;
							} else {
								pre2 = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
										BinaryExpression.Operator.LOGICAND, pre, neq);
							}
						}
						final Expression po1 = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.COMPPO, var, c1id);
						final Expression po2 = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.COMPPO, var2, c2id);
						final Expression lhs = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.LOGICAND, po1, po2);
						final Expression diseq = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.COMPNEQ, var, var2);
						final Expression impl = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
								BinaryExpression.Operator.LOGICIMPLIES, lhs, diseq);
						final VarList vl = new VarList(null, new String[] { "$$", "$$2" }, asttype);
						final Trigger trigger = new Trigger(null, new Expression[] { po1, po2 });
						Expression ax = new QuantifierExpression(null, PrimitiveType.TYPE_BOOL, true, new String[0],
								new VarList[] { vl }, new Attribute[] { trigger }, impl);
						if (pre2 != null) {
							ax = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
									BinaryExpression.Operator.LOGICIMPLIES, pre2, ax);
						}

						newDecls.add(new Axiom(null, new Attribute[0], ax));
					}
				}
			}
		}
	}

	/**
	 * Add to {@code newDecls} the axiom c1 != c2 for each pair of constant
	 * declarations in {@code cdlist} where c1 and c2 are unique. For these new
	 * axioms we can not determine a location.
	 * 
	 * @param newDecls
	 * @param cdlist
	 */
	private void addUniquenessAxioms(ArrayList<Declaration> newDecls, List<ConstDeclaration> cdlist) {
		final ArrayList<String> identifiers = new ArrayList<String>();
		final HashMap<String, VarList> nodeMap = new HashMap<>();
		final IBoogieType type = cdlist.get(0).getVarList().getType().getBoogieType();
		for (final ConstDeclaration c : cdlist) {
			if (c.isUnique()) {
				for (final String id : c.getVarList().getIdentifiers()) {
					identifiers.add(id);
					nodeMap.put(id, c.getVarList());
				}
			}
		}

		assert nodeMap.size() == identifiers.size();

		for (int i = 0; i < identifiers.size(); i++) {
			final DeclarationInformation declInfo = new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL,
					null);
			final String ident1 = identifiers.get(i);
			final IdentifierExpression id1 = new IdentifierExpression(null, type, ident1, declInfo);
			for (int j = i + 1; j < identifiers.size(); j++) {
				final String ident2 = identifiers.get(j);
				final IdentifierExpression id2 = new IdentifierExpression(null, type, ident2, declInfo);
				final Expression diseq = new BinaryExpression(null, PrimitiveType.TYPE_BOOL,
						BinaryExpression.Operator.COMPNEQ, id1, id2);
				/*
				 * Add the axioms one by one. This prevents the syntax tree from
				 * getting too deep.
				 */
				final Axiom newAxiom = new Axiom(null, new Attribute[0], diseq);
				mBacktranslator.addMapping(nodeMap.get(ident1), newAxiom);
				mBacktranslator.addMapping(nodeMap.get(ident2), newAxiom);
				newDecls.add(newAxiom);
			}
		}
	}

	private void addConstDeclaration(IBoogieType type, ConstDeclaration constDecl) {
		List<ConstDeclaration> declList = mConstDecls.get(type);
		if (declList == null) {
			declList = new ArrayList<ConstDeclaration>();
			mConstDecls.put(type, declList);
		}
		declList.add(constDecl);
	}

	@Override
	public void finish() {
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) {
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Replace with a decent implementation!
		return false;
	}

}
