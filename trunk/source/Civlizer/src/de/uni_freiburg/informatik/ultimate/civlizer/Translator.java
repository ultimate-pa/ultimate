
package de.uni_freiburg.informatik.ultimate.civlizer;

java.util.Arrays

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;

public final class Translator {

    // private static prettyDeclaration

    private static int mStmtCounter;

    public static String translate(Declaration[] declarations) {
        mStmtCounter = 0;
        String result = "";

        for (Declaration dec : declarations) {
            result += Translator.translate(dec);
        }
    }

    private static String translate(TypeDeclaration x) {
        // TODO handle attributes

        if (x.isFinite()) {
            return "type finite " + x.getIdentifier();
        }

        return "type " + x.getIdentifier();
    }

    private static String translate(ConstDeclaration x) {
        // TODO handle attributes
        // improve var stream

        if (x.isUnique()) {
            return x.getVarList().getIdentifiers().stream().reduce("", (acc, c) -> acc + "const unique " + c + ";\n");
        }

        return x.getVarList().getIdentifiers().stream().reduce("", (acc, c) -> acc + "const " + c + ";\n");
    }

    private static String translate(Axiom x) {
        return "";
    }

    private static String translate(FunctionDeclaration x) {
        return "";
    }

    private static String translate(VariableDeclaration x) {
        return "";
    }
}