package de.uni_freiburg.informatik.ultimate.astbuilder;

import java.io.IOException;

/**
 * Emitter for the ACSL AST.
 * @author Markus Lindenmann
 * @since 10.12.2012
 */
public class ACSLEmit extends Emit {
    @Override
    public void emitClassDeclaration(Node node) throws IOException {
        writer.println("public "
                + (node.isAbstract() ? "abstract " : "")
                + "class "
                + node.getName()
                + (node.getParent() != null ? " extends " + node.getParent()
                        : " extends ACSLNode") + " {");
    }

    @Override
    public void emitPreamble(Node node) throws IOException {
        super.emitPreamble(node);
        writer.println("import java.util.List;");
        if (node.getParent() == null)
            writer.println("import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;");

    }

    @Override
    public void emitNodeHook(Node node) throws IOException {
        writer.println();
        writer.println("    public List<Object> getChildren() {");
        writer.println("        List<Object> children = super.getChildren();");
        Parameter[] parameters = node.getParameters();
        for (int i = 0; i < parameters.length; i++) {
            writer.println("        children.add(" + parameters[i].getName()
                    + ");");
        }
        writer.println("        return children;");
        writer.println("    }");
    }
}
