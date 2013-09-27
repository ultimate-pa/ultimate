package PatternLanguage;

public class Requirement {
	
	private String reqName;
	private String req;
	
	public Requirement(String reqName, String req){
		this.reqName = reqName;
		this.req = req;
	}
	
	public String getReqName(){
		return this.reqName;
	}
	
	public String getReq(){
		return this.req;
	}
	
}
