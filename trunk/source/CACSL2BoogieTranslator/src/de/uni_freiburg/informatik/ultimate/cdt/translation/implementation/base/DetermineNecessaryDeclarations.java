package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * @author Markus Lindenmann
 * @date 12.12.2012
 */
public class DetermineNecessaryDeclarations extends ASTVisitor {
   /**
     * The symbol table for this class
     */
    ScopedHashMap<String, IASTNode> sT;
    /**
     * The table containing all functions.
     */
    private LinkedHashMap<String, IASTFunctionDefinition> functionTable;
    
    
    
    Stack<IASTNode> currentFunOrStructDef;
    
    LinkedHashMap<IASTNode, LinkedHashSet<IASTNode>> dependencyGraph;
    
    LinkedHashMap<String, IASTNode> dependencyGraphPreliminaryInverse;
    
    LinkedHashSet<IASTNode> reachableDeclarations;
    
    public boolean isIntArrayRequiredInMM() {
		return isIntArrayRequiredInMM;
	}

	public boolean isFloatArrayRequiredInMM() {
		return isFloatArrayRequiredInMM;
	}

	public boolean isPointerArrayRequiredInMM() {
		return isPointerArrayRequiredInMM;
	}

	boolean isIntArrayRequiredInMM;
    boolean isFloatArrayRequiredInMM;
    boolean isPointerArrayRequiredInMM;
    
    MainDispatcher mainDispatcher;
    
    /**
     * Constructor.
     */
    public DetermineNecessaryDeclarations(MainDispatcher main) {
    	this.shouldVisitParameterDeclarations = true;
    	this.shouldVisitTranslationUnit = true;
        this.shouldVisitDeclarations = true;
        this.shouldVisitExpressions = true;
        this.shouldVisitStatements = true;
        this.sT = new ScopedHashMap<String, IASTNode>();
        this.functionTable = new LinkedHashMap<>();
        this.dependencyGraph = new LinkedHashMap<>();
        this.dependencyGraphPreliminaryInverse = new LinkedHashMap<>();
        this.reachableDeclarations = new LinkedHashSet<>();
        this.isIntArrayRequiredInMM = false;
        this.isFloatArrayRequiredInMM = false;
        this.mainDispatcher = main;
        this.currentFunOrStructDef = new Stack<>();
    }
    
    @Override
	public int visit(IASTParameterDeclaration declaration) {
    	if (!currentFunOrStructDef.isEmpty()) {
    		IASTDeclSpecifier declSpec = declaration.getDeclSpecifier();
    		if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
    			IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
    			String name = elts.getName().toString();
    			IASTNode decOfName = sT.get(name);
    			if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
    				addDependency(currentFunOrStructDef.peek(), decOfName);
    				addDeclSpecifierDependencyAlongWithDeclaration(currentFunOrStructDef.peek(),decOfName);
    			}
    		} else if (declSpec instanceof IASTNamedTypeSpecifier) {
    			IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
    			String name = nts.getName().toString();
    			IASTNode decOfName = sT.get(name);
    			if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
    				addDependency(currentFunOrStructDef.peek(), decOfName);
    				addDeclSpecifierDependencyAlongWithDeclaration(currentFunOrStructDef.peek(),decOfName);

    			}
    		}
    	}
    	return super.visit(declaration);
	}

	@Override
    public int visit(IASTExpression expression) {
    	if (expression instanceof IASTIdExpression) {
    		return this.visit((IASTIdExpression) expression);
    	} else if (expression instanceof IASTFunctionCallExpression) {
    		return this.visit((IASTFunctionCallExpression) expression);
    	} else {
    		return super.visit(expression);
    	}
    }

    public int visit(IASTIdExpression expression) {
    	String symbolName = expression.getName().toString();
    	IASTNode symbolDec = sT.get(symbolName);
    	if (symbolDec != null)
//    		dependencyGraph.put(currentFunDef, symbolDec);
    		addDependency(currentFunOrStructDef.peek(), symbolDec);
    	else
    		dependencyGraphPreliminaryInverse.put(symbolName, currentFunOrStructDef.peek());
        return super.visit(expression);
    }
    

	public int visit(IASTFunctionCallExpression expression) {
    	IASTExpression funNameEx = expression.getFunctionNameExpression();
    	if (funNameEx instanceof IASTIdExpression) {
    		IASTIdExpression idEx = (IASTIdExpression) funNameEx;
    		IASTFunctionDefinition funcTableEntry = functionTable.get(idEx.getName().toString());
    		if (funcTableEntry != null)
    			//    			dependencyGraph.put(currentFunDef, funcTableEntry);
    			addDependency(currentFunOrStructDef.peek(), funcTableEntry);
    		IASTNode sTEntry = sT.get(idEx.getName().toString());
    		if (sTEntry != null)
    			//    			dependencyGraph.put(currentFunDef, (IASTDeclaration) sTEntry);
    			addDependency(currentFunOrStructDef.peek(), sTEntry);
    		if (sTEntry == null && funcTableEntry == null) //we have to delay making the entry in the dependency graph
    			dependencyGraphPreliminaryInverse.put(idEx.getName().toString(), currentFunOrStructDef.peek());
    	} else {
    		throw new NotImplementedException(); //TODO: handle calls via function pointers
    	}
    	return super.visit(expression);
	}

	@Override
	public int visit(IASTDeclaration declaration) {
		if (declaration instanceof CASTSimpleDeclaration) {
			boolean decIsGlobal = declaration.getParent() instanceof IASTTranslationUnit;
			CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
			IASTDeclSpecifier declSpec = cd.getDeclSpecifier();


			if (decIsGlobal) { //global declaration
				
				//if we have a global declaration of a structType with a name
				// for example: struct s { int x; };
				// we have to remember that struct name
				if (declSpec instanceof IASTCompositeTypeSpecifier) {
					IASTCompositeTypeSpecifier cts = (IASTCompositeTypeSpecifier) declSpec;
					String declSpecName = cts.getName().toString();
					if (!declSpecName.isEmpty()) {
//						sT.put(declSpecName, declSpec);//two times put with the same key..
						sT.put(declSpecName, declaration);
					}
					
					for (String id : dependencyGraphPreliminaryInverse.keySet()) {
						if (declSpecName.equals(id)) {
							addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
							addDependency(dependencyGraphPreliminaryInverse.get(id), declSpec);//TODO understand this
						}
					}
				}
				
				// each declarator of a global declaration has to be stored in the symbolTable
				// --> we check all uses in IdExpression and add a dependecy to the declarator accordingly
				// the symbolTable connects identifer and declarator
				for (IASTDeclarator d : cd.getDeclarators()) {
					String declaratorName = d.getName().toString();
					sT.put(declaratorName, d);

					for (String id : dependencyGraphPreliminaryInverse.keySet()) {
						if (declaratorName.equals(id)) {
							addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
						}
					}
				}
			} else { //local declaration
				//if we use a globally defined type, this introduces a dependency 
				if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
					IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
					String name = elts.getName().toString();
					IASTNode decOfName = sT.get(name);
					if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
						addDependency(currentFunOrStructDef.peek(), decOfName);
						addDeclSpecifierDependencyAlongWithDeclaration(currentFunOrStructDef.peek(),decOfName);
					}

				} else if (declSpec instanceof IASTNamedTypeSpecifier) {
					IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
					String name = nts.getName().toString();
					IASTNode decOfName = sT.get(name);
					if (decOfName != null) { //if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway
						addDependency(currentFunOrStructDef.peek(), decOfName);
						//add DEclspecifiers for good measure..
						addDeclSpecifierDependencyAlongWithDeclaration(currentFunOrStructDef.peek(),decOfName);
					}

				} 
			}
			//global or local
			for (IASTDeclarator d : cd.getDeclarators()) {
				// "typedef declSpec declarators" introduces a dependency from each declarator to 
				// - the declspec itself it it is a compositeType
				// - the declspec's sT entry otherwise
				//				if (declSpec.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
				//case: the declSpecifier references a declaration we have to add to the dependencyGraph
				String declSpecName = "";
				if (declSpec instanceof IASTSimpleDeclSpecifier) {
					addDependency(d, declSpec); //not needed for what delcarations are made but for computing the memory model requirements
					addDependency(d, declaration); //not needed for what delcarations are made but for computing the memory model requirements
				} else if (declSpec instanceof IASTElaboratedTypeSpecifier) {//i.e. sth like struct/union/enum typename varname
					IASTElaboratedTypeSpecifier elts = (IASTElaboratedTypeSpecifier) declSpec;
					declSpecName = elts.getName().toString();
					IASTNode decOfName = sT.get(declSpecName);
					if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway (most cases..)
						addDependency(d, sT.get(declSpecName));
						addDeclSpecifierDependencyAlongWithDeclaration(d, decOfName);
					}
					else if (decOfName == null && 
							decIsGlobal)
						dependencyGraphPreliminaryInverse.put(declSpecName, d);
				} else if (declSpec instanceof IASTNamedTypeSpecifier) {
					IASTNamedTypeSpecifier nts = (IASTNamedTypeSpecifier) declSpec;
					declSpecName = nts.getName().toString();
					IASTNode decOfName = sT.get(declSpecName);
					if (decOfName != null) {//if it is null, it must reference to a local declaration (of the same scope..) that we keep anyway (most cases..)
						addDependency(d, decOfName);
						addDeclSpecifierDependencyAlongWithDeclaration(d, decOfName);
					}
					else if (decOfName == null && 
							decIsGlobal)
						dependencyGraphPreliminaryInverse.put(declSpecName, d);
				} else if (declSpec instanceof IASTCompositeTypeSpecifier) {
					//						IASTCompositeTypeSpecifier cts = (IASTCompositeTypeSpecifier) declSpec;
					//						declSpecName = cts.getName().toString();
					//						addDependency(d, cts);
					addDependency(d, declSpec);
				}
				//				}
				//case: the declarator references a declaration we have to add to the dependency graph
//				if (d instanceof IASTFunctionDeclarator) { --> is handled in a separate visitor
//					IASTFunctionDeclarator funDec = (IASTFunctionDeclarator) d;
//					
//				}


			}
			if (declSpec instanceof IASTCompositeTypeSpecifier) {
//				currentFunOrStructDef.push(declSpec);
				currentFunOrStructDef.push(declaration);
			}
		} else if (declaration instanceof IASTFunctionDefinition) {
			IASTFunctionDefinition funDef = (IASTFunctionDefinition)declaration;
			functionTable.put(funDef.getDeclarator().getName().toString(), funDef);

			if (declaration.getParent() instanceof IASTTranslationUnit) {
				for (String id : dependencyGraphPreliminaryInverse.keySet()) {
					if (funDef.getDeclarator().getName().toString().equals(id)) {
						//            		dependencyGraph.put(dependencyGraphPreliminaryInverse.get(id), declaration);
						addDependency(dependencyGraphPreliminaryInverse.get(id), declaration);
						//            		dependencyGraphPreliminaryInverse.remove(id);
					}
				}
			}

			sT.beginScope();
			if (funDef.getDeclarator() instanceof CASTFunctionDeclarator) {
				CASTFunctionDeclarator dec =
						(CASTFunctionDeclarator)funDef.getDeclarator();
				for (IASTParameterDeclaration param : dec.getParameters()) {
					String key = param.getDeclarator().getName().toString();
					sT.put(key, param);
				}
			}
			currentFunOrStructDef.push(funDef);
			int nr = super.visit(declaration);
			sT.endScope();
			return nr;
		}
		return super.visit(declaration);
	}

	private void addDeclSpecifierDependencyAlongWithDeclaration(IASTNode source,
			IASTNode target ) {
		if (source instanceof IASTSimpleDeclaration) {
			addDependency(
				((IASTSimpleDeclaration) source).getDeclSpecifier(),
				target);
		} else if (source instanceof IASTFunctionDefinition) {
			addDependency(
				((IASTFunctionDefinition) source).getDeclSpecifier(),
				target);	
		}
	}

	@Override
    public int leave(IASTDeclaration declaration) {
        if (declaration instanceof IASTFunctionDefinition) {
        	currentFunOrStructDef.pop();
        } else if (declaration instanceof IASTSimpleDeclaration) {
        	if (((IASTSimpleDeclaration) declaration).getDeclSpecifier() 
        			instanceof IASTCompositeTypeSpecifier) {
        		currentFunOrStructDef.pop();
        	}
        }
        return super.leave(declaration);
    }
 
    @Override
    public int visit(IASTStatement statement) {
        if (statement instanceof IASTCompoundStatement
                && !(statement.getParent() instanceof IASTFunctionDefinition || statement
                        .getParent() instanceof IASTForStatement)) {
            // the scope for IASTFunctionDefinition and IASTForStatement was
            // opened in parent before!
            sT.beginScope();
            int nr = super.visit(statement);
            sT.endScope();
            return nr;
        }
        if (statement instanceof IASTSwitchStatement) {
            sT.beginScope();
            int nr = super.visit(statement);
            sT.endScope();
            return nr;
        }
        if (statement instanceof IASTForStatement) {
            sT.beginScope();
            int nr = super.visit(statement);
            sT.endScope();
            return nr;
        }
        return super.visit(statement);
    }
    
    @Override
    public int leave(IASTTranslationUnit tu) {
    	int result = super.leave(tu);
    	//compute set from graph
    	computeReachableSetAndUpdateMMRequirements();
    	return result;
    }
    
    private void addDependency(IASTNode declaration, IASTNode symbolDec) {
    	assert declaration != null;
    	assert symbolDec != null;
//    	assert declaration != symbolDec; //structs may actually depend on themselves --> does not hurt..
    			
    	LinkedHashSet<IASTNode> set = dependencyGraph.get(declaration);
    	if (set == null) {
    		set = new LinkedHashSet<>();
    	}
    	set.add(symbolDec);
    	dependencyGraph.put(declaration, set);
	}

    String prettyPrintDependencyGraph() {
    	StringBuilder sb = new StringBuilder();
    	for (Entry<IASTNode, LinkedHashSet<IASTNode>> entry : dependencyGraph.entrySet()) {
    		for (IASTNode n : entry.getValue()) {
    			sb.append(entry.getKey() == null ? "null" : entry.getKey().getRawSignature());
    			sb.append("\n -> \n");
//    			s += entry.getValue().getRawSignature();
    			sb.append(n == null ? "null" : n.getRawSignature());
    			sb.append("\n\n--------\n");
    		}
    	}
    	return sb.toString();
    }
    
    String prettyPrintDependencyGraphFilter(String filter, int maxlength) {
    	StringBuilder sb = new StringBuilder();
    	for (Entry<IASTNode, LinkedHashSet<IASTNode>> entry : dependencyGraph.entrySet()) {
    		for (IASTNode n : entry.getValue()) {
    			
    			String source = entry.getKey() == null ? "null" : entry.getKey().getRawSignature();
    			source = source.substring(0, maxlength < source.length() ? maxlength : source.length());
    			String target = n == null ? "null" : n.getRawSignature();
    			target = target.substring(0, maxlength < target.length() ? maxlength : target.length());
    			if (source.contains(filter) || target.contains(filter)) {
    				sb.append(source);
    				sb.append("\n -> \n");
    				//    			s += entry.getValue().getRawSignature();
    				sb.append(target);
    				sb.append("\n\n--------\n");
    			}
    		}
    	}
    	return sb.toString();
    }
    
    String prettyPrintReachableSet() {
    	StringBuilder sb = new StringBuilder();
    	for (IASTNode node : reachableDeclarations) {
    		sb.append(node.getRawSignature());
    		sb.append("\n\n--------\n");
    	}
    	return sb.toString();
    }
    
    String prettyPrintReachableSetFilter(String filter) {
    	StringBuilder sb = new StringBuilder();
    	for (IASTNode node : reachableDeclarations) {
    		String nodeString = node.getRawSignature();
    		if (nodeString.contains(filter)) {
    			sb.append(nodeString);
    			sb.append("\n\n--------\n");
    		}
    	}
    	return sb.toString();
    }
      
    String prettyPrintSymbolTable() {
    	StringBuilder sb = new StringBuilder();
    	for (Entry<String, IASTNode> x : sT.entrySet()) {
    		sb.append(x.getKey() + " --> " + x.getValue().getRawSignature() + "\n");
    	}
    	return sb.toString();
    }
    
    void computeReachableSetAndUpdateMMRequirements() {
    	LinkedHashSet<String> entryPoints = new LinkedHashSet<>();//TODO: replace with input from settings
    	entryPoints.add("main");
    	
    	ArrayDeque<IASTNode> openNodes = new ArrayDeque<>();
    	
    	for (String ep : entryPoints) {
    		openNodes.add(functionTable.get(ep));
    	}
    	
    	while(!openNodes.isEmpty()) {
    		IASTNode currentNode = openNodes.pollFirst();
    		reachableDeclarations.add(currentNode);
    		LinkedHashSet<IASTNode> targets = dependencyGraph.get(currentNode);
    		if (targets != null) {
    			for (IASTNode targetNode : targets) {
    				if (!reachableDeclarations.contains(targetNode)) {
    					openNodes.add(targetNode);
    					updateMMRequirements(targetNode);
    				}
    			}
    		}
    	}
    }
    
    private void updateMMRequirements(IASTNode reachableNode) {
    	IASTDeclaration decl = null;
    	
    	//determine DeclarationSpecifier (either of parent declaration or declaration itself)
    	IASTDeclSpecifier declSpec = null;
    	ArrayList<IASTDeclarator> declarators = new ArrayList<>();
    	if (reachableNode instanceof IASTDeclarator) {
    		decl = (IASTDeclaration) reachableNode.getParent();//take the Declaration instead
    		declarators.add((IASTDeclarator) reachableNode);
    	} else if (reachableNode instanceof IASTDeclaration){
    		decl = (IASTDeclaration) reachableNode;
    	}
    	if (decl instanceof IASTSimpleDeclaration) {
    		IASTSimpleDeclaration sDec = (IASTSimpleDeclaration) decl;
    		if (sDec.getDeclarators().length == 0)
    			return;
    		declarators.addAll(Arrays.asList(sDec.getDeclarators()));
    		declSpec = sDec.getDeclSpecifier();
    	} else if (decl instanceof IASTFunctionDefinition) {
    		IASTFunctionDefinition fDef = (IASTFunctionDefinition) decl;    			
    		declarators.add(fDef.getDeclarator());
    		declSpec = fDef.getDeclSpecifier();
    	}

    	for (IASTDeclarator declarator : declarators) {
    		if (declSpec instanceof IASTSimpleDeclSpecifier) {
    			ResultTypes rt = (ResultTypes) mainDispatcher.dispatch(declSpec);
    			switch (declarator.getPointerOperators().length) {
    			case 0:
    				//not a pointer -> no consequences for memory model
    				break;
    			case 1:
    				//simple pointer -> check declSpec's type
    				if (rt.cType instanceof CPrimitive) {
    					switch (((CPrimitive) rt.cType).getGeneralType()) {
    					case FLOATTYPE:
    						isFloatArrayRequiredInMM = true;
    						break;
    					case INTTYPE:
    						isIntArrayRequiredInMM = true;
    						break;
    					default:
    						//do nothing
    						break;
    					}
    				}
    				break;
    			default:
    				//pointer to pointer -> pointer array necessary in memory model
    				isPointerArrayRequiredInMM = true;
    				break;
    			}
    		}
    	}
	}

	LinkedHashSet<IASTNode> getReachableDeclarationsOrDeclarators() {
    	return reachableDeclarations;
    }
}
