package local.stalin.astbuilder;

import java.io.IOException;

public class StalinEmit extends Emit {
	public StalinEmit(Grammar grammar) {
		super(grammar);
	}

	/* (non-Javadoc)
	 * @see local.stalin.astbuilder.Emit#emitClassDeclaration(local.stalin.astbuilder.Node)
	 */
	//@Override
	public void emitClassDeclaration(Node node) throws IOException {
        writer.println("public "+ (node.isAbstract() ? "abstract ": "")+ 
                "class "+node.getName()+
                ( node.getParent() != null ? " extends "+node.getParent()
                  : " extends ASTNode") + " {");
        writer.println("    private static final long serialVersionUID = 1L;");
	}

	/* (non-Javadoc)
	 * @see local.stalin.astbuilder.Emit#emitPreamble(local.stalin.astbuilder.Node)
	 */
	//@Override
	public void emitPreamble(Node node) throws IOException {
		super.emitPreamble(node);
		writer.println("import java.util.List;");
		if (node.getParent() == null)
			writer.println("import local.stalin.model.boogie.ast.wrapper.ASTNode;");
	}

	public void emitNodeHook(Node node) throws IOException {
		writer.println();
		writer.println("    public List<Object> getChildren() {");
		writer.println("        List<Object> children = super.getChildren();");
		Parameter[] parameters = node.getParameters();	
		for (int i = 0; i < parameters.length; i++) {
			writer.println("        children.add("+parameters[i].getName() +");"); 
		}
		writer.println("        return children;");
		writer.println("    }");
	}
	
}
