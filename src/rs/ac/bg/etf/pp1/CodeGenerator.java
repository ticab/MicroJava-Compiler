package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class CodeGenerator extends VisitorAdaptor {
	private int mainPc;
	private Stack<List<Integer>> orBlock = new Stack<>();
	private Stack<List<Integer>> andBlock = new Stack<>();
	private Stack<List<Integer>> thenBlock = new Stack<>();
	private Stack<Integer> forIncAdr = new Stack<>();
	private Stack<Integer> forCondSt = new Stack<>();
	private Stack<List<Integer>> forEnd = new Stack<>();
	private List<Obj> unpack = new ArrayList<>();
	private Map<String, Integer> mapa = new HashMap<>();
	private int vel = 0;
	private String arname = null;
	private boolean noLoad = false;

	public int getMainPc() {
		return mainPc;
	}

	// MethodDecl -----------------------------------------------------------------

	@Override
	public void visit(MethodFullName methodFullName) {
		if ("main".equals(methodFullName.getMethodName())) {
			mainPc = Code.pc;
		}
		methodFullName.obj.setAdr(Code.pc);

		Code.put(Code.enter);
		Code.put(methodFullName.obj.getLevel()); // num of args
		Code.put(methodFullName.obj.getLocalSymbols().size()); // args + local vars

	}

	@Override
	public void visit(MethodDecl methodDecl) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}

	// Statement -----------------------------------------------------------------

	@Override
	public void visit(PrintStatement printStatement) {
		if (printStatement.getExpr().struct == Tab.charType) {
			Code.loadConst(1); // sirina=1
			Code.put(Code.bprint);
		} else {
			Code.loadConst(5);
			Code.put(Code.print);
		}
	}

	@Override
	public void visit(PrintStatementWit printStatementWit) {
		Code.loadConst(printStatementWit.getWidth());
		if (printStatementWit.getExpr().struct == Tab.charType) {
			Code.put(Code.bprint);
		} else {
			Code.put(Code.print);
		}
	}

	@Override
	public void visit(StatementRead statementRead) {
		if (statementRead.getDesignator().obj.getType() == Tab.charType) {
			Code.put(Code.bread);
		} else {
			Code.put(Code.read);
		}
		Code.store(statementRead.getDesignator().obj);
	}

	@Override
	public void visit(StatementReturn StatementReturn) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}

	@Override
	public void visit(StatementReturnExpr StatementReturnExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}

	// DesignatorStatement
	// -----------------------------------------------------------------
	
	@Override
	public void visit(DesStStart DesStStart) {
		noLoad = true;
	}

	@Override
	public void visit(DesignBC designBC) {
		Obj dest = designBC.getDesignator1().obj;
		int j = 0;
		for(int i=0; i<unpack.size(); i++) {
			if(unpack.get(i).getName().equals("comma")) {
				j++;
			}
			else if(unpack.get(i).getName().equals("expr")) {
				i++;
				Code.load(unpack.get(i));
				i++;
				if(unpack.get(i).getName().equals("expr")) {
					i++;
					Code.load(unpack.get(i));
					i++;
					Code.loadConst(Integer.parseInt(unpack.get(i).getName()));
					Code.put(Code.aload);
				}
				else {
					Code.loadConst(Integer.parseInt(unpack.get(i).getName()));
				}
				Code.load(dest);
				Code.loadConst(j);
				Code.put(Code.aload);
				Code.put(Code.astore);
				j++;
			}
			else {
				Code.load(dest);
				Code.loadConst(i);
				Code.put(Code.aload); 
				Code.store(unpack.get(i));
				j++;
			}
		}
		unpack.clear();
		noLoad = false;
		int j1 = 0;
		Obj d2 = designBC.getDesignator().obj;
		while(j1<mapa.get(d2.getName())) {
			Code.load(d2);
			Code.loadConst(j1);
			
			Code.load(dest);
			Code.loadConst(j);
			
			Code.put(Code.aload);
			Code.put(Code.astore);
			j++; j1++;
		}
	}
	
	@Override
	public void visit(DesStWithDes desStWithDes) {
		if(!(desStWithDes.getDesignator() instanceof DesigWithExpr))
			unpack.add(desStWithDes.getDesignator().obj);
	}
	
	@Override
	public void visit(DesStWithComma desStWithComma) {
		unpack.add(new Obj(4, "comma", Tab.noType));
	}
	
	@Override
	public void visit(DesignAssign designAssign) {
		Code.store(designAssign.getDesignator().obj);
	}

	@Override
	public void visit(DesignFuncCall designFuncCall) {
		Obj functionObj = designFuncCall.getFunctionCallName().obj;
		if (functionObj.getName().equals("len")) {
			Code.put(Code.arraylength);
			return;
		}

		int offset = functionObj.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset);
		if (functionObj.getType() != Tab.noType) {
			Code.put(Code.pop);
		}
	}

	@Override
	public void visit(DesignPostInc designPostInc) {
		if (designPostInc.getDesignator().obj.getKind() == Obj.Var) {
			Code.load(designPostInc.getDesignator().obj);
		} else if (designPostInc.getDesignator().obj.getKind() == Obj.Elem) {
			Code.put(Code.dup2); // za store + za aload
			Code.load(designPostInc.getDesignator().obj); // niz[i]
		}
		Code.loadConst(1);
		Code.put(Code.add);
		Code.store(designPostInc.getDesignator().obj);
	}

	@Override
	public void visit(DesignPostDec designPostDec) {
		if (designPostDec.getDesignator().obj.getKind() == Obj.Var) {
			Code.load(designPostDec.getDesignator().obj);
		} else if (designPostDec.getDesignator().obj.getKind() == Obj.Elem) {
			Code.put(Code.dup2);
			Code.load(designPostDec.getDesignator().obj);
		} 
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.store(designPostDec.getDesignator().obj);
	}

	@Override
	public void visit(StatementBreak StatementBreak) {
		Code.putJump(0);
		forEnd.peek().add(Code.pc-2);
	}

	@Override
	public void visit(StatementContinue StatementContinue) {
		Code.putJump(forIncAdr.peek());
	}

	@Override
	public void visit(StartIf StartIf) {
		orBlock.push(new ArrayList<>());
		andBlock.push(new ArrayList<>());
		thenBlock.push(new ArrayList<>());
	}

	@Override
	public void visit(EndIf EndIf) {
		for (int adr : orBlock.peek()) {
			Code.fixup(adr);
		}
		orBlock.peek().clear();
	}

	@Override
	public void visit(EmptyIfElse emptyIfElse) {
		if(emptyIfElse.getParent() instanceof StatementIfElse) {
			Code.putJump(0); //ako je if ispunjen
			thenBlock.peek().add(Code.pc-2);
		}
		for(int adr: andBlock.peek()) {
			Code.fixup(adr);
		}
		andBlock.peek().clear();
	}

	@Override
	public void visit(StatementIf StatementIf) {
		andBlock.pop();
		orBlock.pop();
		thenBlock.pop();
	}

	@Override
	public void visit(StatementIfElse StatementIfElse) {
		for (int adr : thenBlock.peek()) {
			Code.fixup(adr);
		}
		thenBlock.peek().clear();
		thenBlock.pop();
		andBlock.pop();
		orBlock.pop();
	}
	@Override
	public void visit(ForStart ForStart) {
		andBlock.push(new ArrayList<>());
		thenBlock.push(new ArrayList<>());
		forEnd.push(new ArrayList<>());
	}
	
	@Override
	public void visit(ForStartStm ForStartStm) {
		for (int adr : thenBlock.peek()) {
			Code.fixup(adr);
		}
		thenBlock.peek().clear();
	}
	
	@Override
	public void visit(ForStartInc forStartInc) {
		forIncAdr.push(Code.pc);
	}
	
	@Override
	public void visit(ForCondStart forCondStart) {
		forCondSt.push(Code.pc);
	}
	
	@Override
	public void visit(StatementFor StatementFor) {
		Code.putJump(forIncAdr.pop());
		for(int adr: forEnd.peek()) {
			Code.fixup(adr);
		}
		for (int adr : andBlock.peek()) {
			Code.fixup(adr);
		}
		forEnd.peek().clear();
		andBlock.peek().clear();
		andBlock.pop();
		thenBlock.pop();
	}
	
	@Override
	public void visit(ForEndInc ForEndInc) {
		Code.putJump(forCondSt.pop());
	}
	
	@Override
	public void visit(WithCondFact forCondFact) {
		Code.putJump(0);
		thenBlock.peek().add(Code.pc-2);
	}
	
	@Override
	public void visit(EmptyCondFact EmptyCondFact) {
		Code.loadConst(1); // true
		Code.putJump(0);
		thenBlock.peek().add(Code.pc-2);
	}

	// Condition -----------------------------------------------------------------

	@Override
	public void visit(OrBlock OrBlock) {
		Code.putJump(0); //true
		orBlock.peek().add(Code.pc - 2);
		for (int adr : andBlock.peek()) {
			Code.fixup(adr);
		}
		andBlock.peek().clear();
	}

	@Override
	public void visit(RelopCondF relopCondF) {
		if (relopCondF.getRelop() instanceof EqualOper)
			Code.putFalseJump(Code.eq, 0);
		else if (relopCondF.getRelop() instanceof NotEqualOp)
			Code.putFalseJump(Code.ne, 0);
		else if (relopCondF.getRelop() instanceof LessOp)
			Code.putFalseJump(Code.lt, 0);
		else if (relopCondF.getRelop() instanceof LessEqOp)
			Code.putFalseJump(Code.le, 0);
		else if (relopCondF.getRelop() instanceof GreaterOp)
			Code.putFalseJump(Code.gt, 0);
		else if (relopCondF.getRelop() instanceof GreaterEqOp)
			Code.putFalseJump(Code.ge, 0);
		andBlock.peek().add(Code.pc - 2);
	}

	@Override
	public void visit(SingleCondF SingleCondF) {
		Code.loadConst(1); // true
		Code.putFalseJump(Code.eq, 0);
		andBlock.peek().add(Code.pc - 2);
	}

	// Expr -----------------------------------------------------------------

	@Override
	public void visit(NegativeExpr NegativeExpr) {
		Code.put(Code.neg);
	}

	@Override
	public void visit(AddExpr addExpr) {
		if (addExpr.getAddop() instanceof PlusOper)
			Code.put(Code.add);
		else
			Code.put(Code.sub);
	}

	// Factor -----------------------------------------------------------------

	@Override
	public void visit(MulFactors mulFactors) {
		if (mulFactors.getMulop() instanceof MulOper)
			Code.put(Code.mul);
		else if (mulFactors.getMulop() instanceof DivOper)
			Code.put(Code.div);
		else
			Code.put(Code.rem);
	}

	@Override
	public void visit(FactorVar factorVar) {
		if(!noLoad)
			Code.load(factorVar.getDesignator().obj);
	}

	@Override
	public void visit(FactorFuncCall factorFuncCall) {
		Obj functionObj = factorFuncCall.getFunctionCallName().obj;
		if (functionObj.getName().equals("chr")) {
			return;
		} else if (functionObj.getName().equals("ord")) {
			return;
		} else if (functionObj.getName().equals("len")) {
			Code.put(Code.arraylength);
			return;
		}

		int offset = functionObj.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset);
	}

	@Override
	public void visit(FactorNum factorNum) {
		Obj con = Tab.insert(Obj.Con, Integer.toString(factorNum.getConstValue()), Tab.intType);
		con.setLevel(0);
		con.setAdr(factorNum.getConstValue());
		if(!noLoad) {
			Code.load(con);
		}
		else {
			unpack.add(con);
		}
		vel = factorNum.getConstValue();
	}

	@Override
	public void visit(FactorChar factorChar) {
		Obj con = Tab.insert(Obj.Con, "$", Tab.charType);
		con.setLevel(0);
		con.setAdr(factorChar.getConstValue());

		Code.load(con);
	}

	@Override
	public void visit(FactorBool factorBool) {
		Obj con = Tab.insert(Obj.Con, "$", TabExtended.boolType);
		con.setLevel(0);
		if (factorBool.getConstValue() == true)
			con.setAdr(1);
		else
			con.setAdr(0);

		Code.load(con);
	}

	public String structName(Struct s) {
		switch (s.getKind()) {
		case Struct.None:
			return "none";
		case Struct.Int:
			return "int";
		case Struct.Char:
			return "char";
		case Struct.Array:
			return "array";
		case Struct.Class:
			return "class";
		case Struct.Bool:
			return "bool";
		case Struct.Enum:
			return "enum";
		case Struct.Interface:
			return "interface";
		default:
			return "";
		}

	}

	@Override
	public void visit(NewArray newArray) {
		Code.put(Code.newarray);
		mapa.put(arname, vel);
		if (newArray.struct.getElemType() == Tab.charType) {
			Code.put(0);
		} else
			Code.put(1);
	}

	// Designator -----------------------------------------------------------------
	@Override
	public void visit(WithDC withDC) {
		arname = withDC.obj.getName();
		if (withDC.getParent() instanceof DesigWithExpr) {
			if(!noLoad) {
				Code.load(withDC.obj);
			}
			else {
				unpack.add(new Obj(4, "expr", Tab.noType));
				unpack.add(withDC.obj);
			}
			
		}
	}

	@Override
	public void visit(WithoutDC withoutDC) {
		arname = withoutDC.obj.getName();
		if (withoutDC.getParent() instanceof DesigWithExpr) {
			if(!noLoad) {
				Code.load(withoutDC.obj);
			}
			else {
				unpack.add(new Obj(4, "expr", Tab.noType));
				unpack.add(withoutDC.obj);
			}
		}
	}
}
