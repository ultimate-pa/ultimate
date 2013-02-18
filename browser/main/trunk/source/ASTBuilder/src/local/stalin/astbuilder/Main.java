package local.stalin.astbuilder;
import java.io.*;

public class Main {
    public void usage() {
        System.err.println("java TreeBuilder.Main <filename> ...");
    }

    public Main(String[] param) throws Exception {
        if (param.length == 0) {
            usage();
            System.exit(1);
            return;
        }
        boolean debug = false;
        int i = 0;
        if (param[i].equals("-debug")) {
            i++;
            debug = true;
        }

        for (; i < param.length; i++) {
            Lexer lexer = new Lexer(new FileReader(param[i]));
            parser p = new parser(lexer);
            p.setFileName(param[i]);
            Grammar grammar;
            if (debug)
                grammar = (Grammar) p.debug_parse().value;
            else
                grammar = (Grammar) p.parse().value;
            if (grammar == null) {
                System.err.println("Parse Error in file: "+param[i]);
                System.exit(1);
            }
            Emit emitter = new StalinEmit(grammar); //TODO configurable
            emitter.emitClasses();
        }
    }

    public static void main(String[] param) throws Exception {
    	new Main(param);
    }

}
