package PatternLanguage;

import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import pea.CDD;
import pea.Decision;
import pea.PhaseEventAutomata;
import pea.modelchecking.TCSWriter;


public class SMV_WriterTCTL extends TCSWriter{
	
	/**
     * FileWriter to output file.
     */
    protected FileWriter writer;

	public SMV_WriterTCTL(String fileName) {
		super(fileName);
		// TODO Auto-generated constructor stub
	}
	

	public void write(RequirementsSet reqSet) {
        try {
            this.writer = new FileWriter(fileName);
            //init();
            writePreamble();
            writeVariables(reqSet);
            writeSpec(reqSet);
            writeClose();
            this.writer.flush();
            this.writer.close();
            System.out.println("Successfully written to "+fileName);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
	 protected void writePreamble() throws IOException {
	        this.writer
	            .write("MODULE main\n"
	                        + " VAR \n"
	                  );
	 }
	 
	 protected void writeVariables(RequirementsSet reqSet) throws IOException{
		 Vector<CDD> variables = reqSet.getVariables();
         for (int i= 0; i< variables.size(); i++){
         	this.writer.write(variables.elementAt(i)+": boolean; \n");
         }
	 }
	 
	 protected void writeSpec(RequirementsSet reqSet) throws IOException{
		 PL_PatternToLTL transformer = new PL_PatternToLTL();
		 this.writer.write("SPEC ");
		 
			for (int i=0; i<reqSet.getReqSetSize(); i++){
				PL_initiatedPattern req = reqSet.getRequirementInitiatedPattern(i);
				transformer.transformPatternToLTL(req);
				String tctl= transformer.getFormulaInTCTL();
				this.writer.write(tctl +" & \n" );
			}
		 
	 }
	 protected void writeClose()throws IOException{
	    	this.writer.write("\n }");
	    }


	@Override
	public void write() {
		// TODO Auto-generated method stub
		
	}


	@Override
	protected void writeAndDelimiter(Writer writer) throws IOException {
		// TODO Auto-generated method stub
		
	}


	@Override
	protected void writeDecision(Decision decision, int child, Writer writer)
			throws IOException {
		// TODO Auto-generated method stub
		
	}

}
