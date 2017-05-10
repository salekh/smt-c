#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class LRAOnly: public Manager
	{
		public:
			LRAOnly(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<LRAModule<LRASettings1>>()
					})
				});
			}
	};
}	// namespace smtrat
