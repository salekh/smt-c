#include <stack>
#include "../../Common.h"
#include "Bound.h"
#include <limits>


namespace smtrat
{

        class TVariable{
			
			
			private:
				
				int id=0;
				
				carl::Variable original;
				FormulaT formula;
				
				Rational value = 0;
				
				//Is stored after succesfull check, to reset for backtrace
				Rational lastValue = 0;
				
				
				Bound upperBound;
				
				Bound lowerBound;
				
				std::stack<Bound> stackUpperBound;
			
				std::stack<Bound> stackLowerBound;
				
				bool isBasic;
				
				bool isSlack;
				
				//used in the method that finds the "problem set" of formulas
				//helps to create the sets N- and N+ as described in the paper
				int positionMatrixX=-1;
				int positionMatrixY=-1;
				
			
	public:
			
				TVariable();
				
				TVariable(FormulaT formula, int pId, bool pIsBasic);
				
				TVariable(carl::Variable pOriginal, int pId, bool pIsBasic);
			
				void changeUpperBound(Bound b);
				
				void changeLowerBound(Bound b);
				
				//reset bounds, loads old value
				void backtrack();
				
				int getId() { return id; };
				
				bool getIsBasic(){return isBasic; };
				void setIsBasic(bool basic){this->isBasic = basic;}
				
				Rational getValue() { return value; };
				void setValue(Rational r) { value = r; };
				
				//Stores and load value/bounds
				void saveValue();
				void saveBounds();
				void load();
				
				void setPositionMatrixX(int positionMatrixX) {this->positionMatrixX = positionMatrixX;}
				void setPositionMatrixY(int positionMatrixY) {this->positionMatrixY = positionMatrixY;}
				int getPositionMatrixX() {return positionMatrixX;}
				int getPositionMatrixY() {return positionMatrixY;}
				
				Bound& getUpperBound() { return upperBound; };
				Bound& getLowerBound() { return lowerBound; };
				
				FormulaT& getFormula() { return formula; };
				
				std::string getName();
		};
}