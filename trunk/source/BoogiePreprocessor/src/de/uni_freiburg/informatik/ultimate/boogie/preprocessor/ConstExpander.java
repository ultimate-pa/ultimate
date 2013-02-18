package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class ConstExpander extends BoogieTransformer 
	implements IUnmanagedObserver {

	
	HashMap<IType, List<ConstDeclaration>> constDecls;

	@Override
	public boolean process(IElement root) {
		if (root instanceof WrapperNode) {
			Unit unit = (Unit) ((WrapperNode) root).getBacking();
			ArrayList<Declaration> newDecls = new ArrayList<Declaration>();
			for (Declaration decl: unit.getDeclarations()) {
				if (decl instanceof ConstDeclaration) {
					ConstDeclaration constDecl = (ConstDeclaration) decl;
					if (!constDecl.isUnique() && constDecl.getParentInfo() == null) {
						newDecls.add(constDecl);
					} else {
						VarList vl = constDecl.getVarList();
						addConstDeclaration(vl.getType().getBoogieType(), constDecl);
						newDecls.add(new ConstDeclaration(
								constDecl.getLocation(),
								constDecl.getAttributes(), false,
								vl, null, false));	
					}
				} else
					newDecls.add(decl);
			}

			for (List<ConstDeclaration> cdlist : constDecls.values()) {
				addUniquenessAxioms(newDecls, cdlist);
				addPartOrderAxioms(newDecls, cdlist);
			}
			unit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			return false;
		}
		return true;
	}
	
	private void addPartOrderAxioms(ArrayList<Declaration> newDecls,
			List<ConstDeclaration> cdlist) {
		HashMap<String, List<String>> childrens = 
			new HashMap<String, List<String>>();
		HashMap<String, List<String>> uniqueChildrens = 
			new HashMap<String, List<String>>();
		HashSet<String> uniqueValues = new HashSet<String>();
		ASTType asttype = cdlist.get(0).getVarList().getType();
		IType type = asttype.getBoogieType();
		IdentifierExpression var = new IdentifierExpression(asttype.getLocation(), type, "$$");
		IdentifierExpression var2 = new IdentifierExpression(asttype.getLocation(), type, "$$2");
		for (ConstDeclaration c : cdlist) {
			ParentEdge[] parents = c.getParentInfo();
			for (String child : c.getVarList().getIdentifiers()) {
				if (c.isUnique())
					uniqueValues.add(child);
				
				if (parents != null) {
					IdentifierExpression cid = new IdentifierExpression(c.getLocation(), type, child);
					Expression polist = null;
					for (ParentEdge p: parents) {
						String parent = p.getIdentifier();
						IdentifierExpression pid = new IdentifierExpression(c.getLocation(), type, parent);
						Expression partorder = new BinaryExpression(c.getLocation(), 
								PrimitiveType.boolType, 
								BinaryExpression.Operator.COMPPO,
								cid, pid);
						if (polist == null)
							polist = partorder;
						else
							polist = new BinaryExpression(c.getLocation(), 
									PrimitiveType.boolType, 
									BinaryExpression.Operator.LOGICAND,
									partorder, polist);
					}
					if (polist != null)
						newDecls.add(new Axiom(c.getLocation(), new Attribute[0], polist));
					polist = new BinaryExpression(c.getLocation(), 
							PrimitiveType.boolType,
							BinaryExpression.Operator.COMPEQ, cid, var);
					for (ParentEdge p: parents) {
						String parent = p.getIdentifier();
						IdentifierExpression pid = new IdentifierExpression(c.getLocation(), type, parent);
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
						Expression partorder = new BinaryExpression(c.getLocation(), 
								PrimitiveType.boolType, 
								BinaryExpression.Operator.COMPPO,
								pid, var);
						polist = new BinaryExpression(c.getLocation(), 
								PrimitiveType.boolType, 
								BinaryExpression.Operator.LOGICOR,
								partorder, polist);
					}
					Expression lhs = new BinaryExpression(c.getLocation(), 
							PrimitiveType.boolType,
							BinaryExpression.Operator.COMPPO, cid, var);
					Expression impl = new BinaryExpression(c.getLocation(), 
							PrimitiveType.boolType,
							BinaryExpression.Operator.LOGICIMPLIES, lhs, polist);
					VarList vl = new VarList(c.getLocation(), new String[] {"$$"}, asttype);
					Trigger trigger = new Trigger(c.getLocation(), new Expression[] {lhs} );
					Expression quant = new QuantifierExpression(c.getLocation(), 
							PrimitiveType.boolType,
							true, new String[0], new VarList[] { vl },
							new Attribute[] { trigger }, impl);
					
					newDecls.add(new Axiom(c.getLocation(),  new Attribute[0], quant));
				}
			}
		}

		for (ConstDeclaration c : cdlist) {
			if (c.isComplete()) {
				for (String parent : c.getVarList().getIdentifiers()) {
					IdentifierExpression pid = new IdentifierExpression(c.getLocation(), type, parent);
					Expression polist = new BinaryExpression(c.getLocation(), 
							PrimitiveType.boolType,
							BinaryExpression.Operator.COMPEQ, var, pid);
					List<String> childList = childrens.get(parent);
					if (childList == null)
						childList = Collections.emptyList();
					for (String child: childList) {
						IdentifierExpression cid = new IdentifierExpression(c.getLocation(), type, child);
						Expression partorder = new BinaryExpression(c.getLocation(), 
								PrimitiveType.boolType, 
								BinaryExpression.Operator.COMPPO,
								var, cid);
						polist = new BinaryExpression(c.getLocation(), 
								PrimitiveType.boolType, 
								BinaryExpression.Operator.LOGICOR,
								partorder, polist);
					}
					Expression lhs = new BinaryExpression(c.getLocation(), 
							PrimitiveType.boolType,
							BinaryExpression.Operator.COMPPO, var, pid);
					Expression impl = new BinaryExpression(c.getLocation(), 
							PrimitiveType.boolType,
							BinaryExpression.Operator.LOGICIMPLIES, lhs, polist);
					VarList vl = new VarList(c.getLocation(), new String[] {"$$"}, asttype);
					Trigger trigger = new Trigger(c.getLocation(), new Expression[] {lhs} );
					Expression quant = new QuantifierExpression(c.getLocation(), 
							PrimitiveType.boolType,
							true, new String[0], new VarList[] { vl },
							new Attribute[] { trigger }, impl);
					
					newDecls.add(new Axiom(c.getLocation(), new Attribute[0], quant));
				}
			}
		}
	
		Collection<String> uniqueParents = uniqueChildrens.keySet();
		for (String p1 : uniqueParents) {
			IdentifierExpression p1id = new IdentifierExpression(null, type, p1);
			Collection<String> p2list = uniqueParents;
			if (uniqueValues.contains(p1))
				p2list = Collections.singleton(p1);
			for (String p2 : p2list) {
				if (!uniqueValues.contains(p2)
					&& p1.compareTo(p2) > 0)
					continue;
				IdentifierExpression p2id;
				Expression pre;
				if (p1.equals(p2)) {
					p2id = p1id;
					pre = null;
				} else {
					p2id = new IdentifierExpression(null, type, p2);
					pre = new BinaryExpression(null, PrimitiveType.boolType,
							BinaryExpression.Operator.COMPEQ,
							p1id, p2id);
				}
				for (String c1 : uniqueChildrens.get(p1)) {
					IdentifierExpression c1id = new IdentifierExpression(null, type, c1);
					for (String c2: uniqueChildrens.get(p2)) {
						if (p1.equals(p2) && c1.compareTo(c2) >= 0
							|| c1.equals(c2))
							continue;
						IdentifierExpression c2id = new IdentifierExpression(null, type, c2);
						Expression pre2 = pre;
						if (!uniqueValues.contains(c1)
							|| !uniqueValues.contains(c2)) {
							Expression neq = new BinaryExpression(null, 
									PrimitiveType.boolType,
									BinaryExpression.Operator.COMPNEQ,
									c1id, c2id);
							if (pre == null)
								pre2 = neq;
							else
								pre2 = new BinaryExpression(null, 
										PrimitiveType.boolType,
										BinaryExpression.Operator.LOGICAND,
										pre, neq);
						}
						Expression po1 = new BinaryExpression(null, 
								PrimitiveType.boolType,
								BinaryExpression.Operator.COMPPO, var, c1id);
						Expression po2 = new BinaryExpression(null, 
								PrimitiveType.boolType,
								BinaryExpression.Operator.COMPPO, var2, c2id);
						Expression lhs = new BinaryExpression(null, 
								PrimitiveType.boolType,
								BinaryExpression.Operator.LOGICAND,
								po1, po2);
						Expression diseq = new BinaryExpression(null, 
								PrimitiveType.boolType,
								BinaryExpression.Operator.COMPNEQ,
								var, var2);
						Expression impl = new BinaryExpression(null, 
								PrimitiveType.boolType,
								BinaryExpression.Operator.LOGICIMPLIES,
								lhs, diseq);
						VarList vl = new VarList(null, new String[] {"$$", "$$2"}, asttype);
						Trigger trigger = new Trigger(null, new Expression[] { po1, po2} );
						Expression ax = new QuantifierExpression(null, 
								PrimitiveType.boolType,
								true, new String[0], new VarList[] { vl },
								new Attribute[] { trigger }, impl);
						if (pre2 != null)
							ax = new BinaryExpression(null, 
									PrimitiveType.boolType,
									BinaryExpression.Operator.LOGICIMPLIES,
									pre2, ax);
						
						newDecls.add(new Axiom(null, new Attribute[0], ax));
					}
				}
			}
		}
	}

	/**
	 * Add to {@code newDecls} the axiom c1 != c2 for each pair of constant
	 * declarations in {@code cdlist} where c1 and c2 are unique.
	 * For these new axioms we can not determine a location.
	 * @param newDecls
	 * @param cdlist
	 */
	private void addUniquenessAxioms(ArrayList<Declaration> newDecls,
			List<ConstDeclaration> cdlist) {
		ArrayList<String> identifiers = new ArrayList<String>();
		IType type = cdlist.get(0).getVarList().getType().getBoogieType();
		for (ConstDeclaration c : cdlist) {
			if (c.isUnique()) {
				for (String id: c.getVarList().getIdentifiers())
					identifiers.add(id);
			}
		}
		for (int i = 0; i < identifiers.size(); i++) {
			IdentifierExpression id1 = 
				new IdentifierExpression(null, type, identifiers.get(i));
			for (int j = i+1; j < identifiers.size(); j++) {
				IdentifierExpression id2 = 
					new IdentifierExpression(null, type, identifiers.get(j));
				Expression diseq = new BinaryExpression(null, PrimitiveType.boolType,
						BinaryExpression.Operator.COMPNEQ, id1, id2);
				/* Add the axioms one by one.  This prevents the syntax tree from getting
				 * too deep.
				 */
				newDecls.add(new Axiom(null, new Attribute[0], diseq));
			}
		}
	}

	private void addConstDeclaration(IType type, ConstDeclaration constDecl) {		
		List<ConstDeclaration> declList = constDecls.get(type);
		if (declList == null) {
			declList = new ArrayList<ConstDeclaration>();
			constDecls.put(type, declList);
		}
		declList.add(constDecl);
	}

	public void finish() {
		constDecls = null;
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init() {
		constDecls = new HashMap<IType, List<ConstDeclaration>>();
	}

	@Override
	public boolean performedChanges() {
		// TODO Replace with a decent implementation!
		return getDefaultPerformedChanges();
	}

	@Deprecated
	private boolean getDefaultPerformedChanges() {
		return false;
	}
	
}
