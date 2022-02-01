
package com.github.jhoenicke.javacup;
import com.github.jhoenicke.javacup.runtime.Symbol;
public class ErrorManager{
    private static ErrorManager errorManager;
    private int errors = 0;
    private int warnings = 0;
    private int fatals = 0;
    public int getFatalCount() { return fatals; }
    public int getErrorCount() { return errors; }
    public int getWarningCount() { return warnings; }
    static {
        errorManager = new ErrorManager();
    }
    public static ErrorManager getManager() { return errorManager; }
    private ErrorManager(){
    }

    //TODO: migrate to java.util.logging
    /**
     * Error message format: 
     * ERRORLEVEL at (LINE/COLUMN)@SYMBOL: MESSAGE
     * ERRORLEVEL : MESSAGE
     **/
    public void emit_fatal(String message){
        System.err.println("Fatal: "+message);
        fatals++;
    }
    public void emit_fatal(String message, Symbol sym){
        System.err.println("Fatal: "+message+" @ "+sym);
        fatals++;
    }
    public void emit_warning(String message){
        System.err.println("Warning: " + message);
        warnings++;	
    }
    public void emit_warning(String message, Symbol sym){
        System.err.println("Warning: " + message+" @ "+sym);
        warnings++;
    }
    public void emit_error(String message){
        System.err.println("Error: " + message);
        errors++;
    }
    public void emit_error(String message, Symbol sym){
        System.err.println("Error: "+message+" @ "+sym);
        errors++;
    }
}
