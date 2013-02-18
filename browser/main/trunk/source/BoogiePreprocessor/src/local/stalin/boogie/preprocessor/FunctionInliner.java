package local.stalin.boogie.preprocessor;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.model.IElement;
import local.stalin.boogie.type.PrimitiveType;
import local.stalin.model.boogie.BoogieTransformer;
import local.stalin.model.boogie.ast.Attribute;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.BinaryExpression;
import local.stalin.model.boogie.ast.Body;
import local.stalin.model.boogie.ast.BooleanLiteral;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.FunctionApplication;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.IdentifierExpression;
import local.stalin.model.boogie.ast.NamedAttribute;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.QuantifierExpression;
import local.stalin.model.boogie.ast.Trigger;
import local.stalin.model.boogie.ast.Unit;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * This class removes function bodies by either inlining them (if the attribute
 * "inline" is set) or by adding a corresponding axiom stating that for all 
 * input values the function returns the output given by the body.
 * 
 * @author hoenicke
 */
public class FunctionInliner extends BoogieTransformer 
	implements IUnmanagedObserver {

	/**
	 * A map containing the functions that should be inlined.  The
	 * key is the function name.
	 */
	HashMap<String, FunctionDeclaration> inlinedFunctions;
	/**
	 * The current scope containing the renamings and names used.
	 */
	Scope currentScope;

	/**
	 * The information for a scope in which renamings may take place.
	 * @author hoenicke
	 */
	private class Scope {
		/**
		 * A renaming is a map from identifier name to expression.
		 */
		private HashMap<String, Expression> renamings;
		/**
		 * The variable names used in the current scope and which therefore
		 * should not be reused in inlined functions.
		 */
		private HashSet<String> declaredName;
		/**
		 * The parent scope.
		 */
		Scope parent;
		
		public Scope() {
			parent = null;
			renamings = new HashMap<String,Expression>();
			declaredName = new HashSet<String>();
		}
		
		public Scope(Scope par) {
			parent = par;
			renamings = new HashMap<String,Expression>(par.renamings);
			declaredName = new HashSet<String>(par.declaredName);
		}
		
		public Scope getParent() {
			return parent;
		}

		public void addRenaming(String name, Expression expr) {
			renamings.put(name, expr);
		}

		public Expression lookupRenaming(String name) {
			// we only need to check current scope, since we clone 
			// renamings when creating a new scope.
			return renamings.get(name);
		}

		public boolean clashes(String name) {
			// we only need to check current scope, since we clone 
			// declaredName when creating a new scope.
			return declaredName.contains(name);
		}
		
		public void declareName(String name) {
			declaredName.add(name);
		}
	}
	

	@Override
	/**
	 * Process a boogie file.  This is called by the tree walker and processes
	 * the main node of the tree that starts the Boogie AST.
	 */
	public boolean process(IElement root) {
		// Check if node is the first node of the AST.
		if (root instanceof WrapperNode) {
			Unit unit = (Unit) ((WrapperNode) root).getBacking();
			List<Declaration> newDeclarations = new ArrayList<Declaration>();
			inlinedFunctions = new HashMap<String, FunctionDeclaration>();
			
			// Process all declarations, copying them and replacing function
			// declarations (removing inlined functions, removing bodies of
			// other functions and adding axioms).
			// It also collects inlined function in the hash map 
			// inlinedFunctions.
			for (Declaration decl: unit.getDeclarations()) {
				if (decl instanceof FunctionDeclaration) {
					FunctionDeclaration fdecl = (FunctionDeclaration) decl;
					if (fdecl.getBody() == null) {
						newDeclarations.add(fdecl);
						continue;
					}
					boolean inlined = false;
					for (Attribute attr : fdecl.getAttributes()) {
						if (attr instanceof NamedAttribute) {
							NamedAttribute nattr = (NamedAttribute) attr;
							Expression[] val = nattr.getValues();
							if (nattr.getName().equals("inline")
								&& val.length == 1
								&& (val[0] instanceof BooleanLiteral)
								&& ((BooleanLiteral) val[0]).getValue()) {
								inlined = true;
								inlinedFunctions.put(fdecl.getIdentifier(), fdecl);
							}
						}
					}
					if (!inlined) {
						List<Expression> params = new ArrayList<Expression>();
						int anonctr = 0;
						for (VarList vl : fdecl.getInParams()) {
							if (vl.getIdentifiers().length == 0) {
								params.add(new IdentifierExpression(vl.getType().getBoogieType(), "#"+(anonctr++)));
							} else {
								for (String i: vl.getIdentifiers()) {
									params.add(new IdentifierExpression(vl.getType().getBoogieType(), i));
								}
							}
						}
						Expression[] funcParams = params.toArray(new Expression[params.size()]); 
						Expression funcApp = new FunctionApplication(fdecl.getOutParam().getType().getBoogieType(), fdecl.getIdentifier(), funcParams);
						Trigger funcTrigger = new Trigger(new Expression[] {funcApp} );
						Expression funcEq = new BinaryExpression(PrimitiveType.boolType, BinaryExpression.Operator.COMPEQ, funcApp, fdecl.getBody());
						Expression funcDecl = new QuantifierExpression(PrimitiveType.boolType, true, fdecl.getTypeParams(), fdecl.getInParams(), new Attribute[] { funcTrigger }, funcEq);
						Axiom fdeclAxiom = new Axiom(fdecl.getFilename(), fdecl.getLineNr(), 
								                     new Attribute[0], funcDecl);
						newDeclarations.add(new FunctionDeclaration(fdecl.getFilename(), fdecl.getLineNr(), 
								fdecl.getAttributes(), fdecl.getIdentifier(), fdecl.getTypeParams(), 
								fdecl.getInParams(), fdecl.getOutParam()));
						newDeclarations.add(fdeclAxiom);
					}
				} else {
					newDeclarations.add(decl);
				}
			}
			// create the outer scope.
			currentScope = new Scope();
			// process all declarations, which does the inlining.
			for (int i = 0; i < newDeclarations.size(); i++) {
				newDeclarations.set(i, processDeclaration(newDeclarations.get(i)));
			}
			currentScope = null;
			inlinedFunctions = null;
			unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
			return false;
		}
		return true;
	}
	
	@Override
	/**
	 * Process a declaration.  This creates new scopes for function and 
	 * procedures, that store input and output variables.
	 */
	protected Declaration processDeclaration(Declaration d)
	{
		if (d instanceof FunctionDeclaration
			|| d instanceof Procedure) {
			currentScope = new Scope(currentScope);
			Declaration result = super.processDeclaration(d);
			currentScope = currentScope.getParent();
			return result;
		} else {
			return super.processDeclaration(d);
		}
	}
	
	@Override
	/**
	 * Process a body.  This creates new scope for storing local variables. 
	 */
	protected Body processBody(Body b)
	{
		currentScope = new Scope(currentScope);
		Body result = super.processBody(b);
		currentScope = currentScope.getParent();
		return result;
	}

	@Override
	/**
	 * Process a variable declaration list.  This adds all variables to 
	 * the name clash set of the current scope. 
	 */
	public VarList processVarList(VarList vl)
	{
		for (String name: vl.getIdentifiers())
			currentScope.declareName(name);
		return super.processVarList(vl);
	}
	
	@Override
	/**
	 * Process an expression.  This replaces identifiers according to the
	 * renaming (if present), inlines function calls, and renames identifiers
	 * in quantifiers in case a name from an inlined function clashes with
	 * a name declared in the outer scope. 
	 */
	public Expression processExpression(Expression expr) {
		if (expr instanceof IdentifierExpression) {
			// rename identifiers according to the renaming map in the scope.
			String name = ((IdentifierExpression) expr).getIdentifier();
			Expression renamed = currentScope.lookupRenaming(name);
			if (renamed != null)
				return renamed;
		} else if (expr instanceof FunctionApplication) {
			// inline function applications
			FunctionApplication app = (FunctionApplication) expr;
			String name = app.getIdentifier();
			if (inlinedFunctions.containsKey(name)) {
				currentScope = new Scope(currentScope);
				FunctionDeclaration fdecl = inlinedFunctions.get(name);
				Expression[] args = app.getArguments();
				int pnr = 0;
				for (VarList vl : fdecl.getInParams()) {
					if (vl.getIdentifiers().length == 0)
						pnr++;
					else {
						for (String i: vl.getIdentifiers()) {
							currentScope.addRenaming(i, processExpression(args[pnr++]));
						}
					}
				}
				Expression newBody = processExpression(fdecl.getBody());
				currentScope = currentScope.getParent();
				return newBody;
			}
		} else if (expr instanceof QuantifierExpression) {
			// check that quantified variables are unique
			QuantifierExpression qexpr = (QuantifierExpression) expr;
			currentScope = new Scope(currentScope);
			VarList[] vl = qexpr.getParameters();
			VarList[] newVl = vl;
			for (int vlNr = 0; vlNr < vl.length; vlNr++) {
				String[] ids = vl[vlNr].getIdentifiers();
				String[] newIds = ids;
				for (int idNr = 0; idNr < ids.length; idNr++) {
					if (currentScope.clashes(ids[idNr])) {
						if (newIds == ids) {
							newIds = ids.clone();
						}
						int ctr = 0;
						String newname;
						do {
							newname = ids[idNr]+"$"+(ctr++);
						} while (currentScope.clashes(newname));
						newIds[idNr] = newname;
						currentScope.addRenaming(ids[idNr], new IdentifierExpression(vl[vlNr].getType().getBoogieType(), newname));
					}
					if (newIds != ids) {
						if (newVl == vl) {
							newVl = vl.clone();
						}
						newVl[vlNr] = new VarList(newIds, vl[vlNr].getType());
					}
				}
			}
			newVl = processVarLists(newVl);
			Expression subform = processExpression(qexpr.getSubformula());
			Attribute[] attrs = processAttributes(qexpr.getAttributes());
			currentScope = currentScope.getParent();
			if (vl == newVl && subform == qexpr.getSubformula() && attrs == qexpr.getAttributes())
				return expr;
			return new QuantifierExpression(qexpr.getType(), qexpr.isUniversal(), 
					qexpr.getTypeParams(), newVl, attrs,
					subform);
		}
		return super.processExpression(expr);
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init() {
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
