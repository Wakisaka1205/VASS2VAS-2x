monad.vo monad.glob monad.v.beautified monad.required_vo: monad.v 
monad.vio: monad.v 
monad.vos monad.vok monad.required_vos: monad.v 
vecop.vo vecop.glob vecop.v.beautified vecop.required_vo: vecop.v 
vecop.vio: vecop.v 
vecop.vos vecop.vok vecop.required_vos: vecop.v 
vectrans.vo vectrans.glob vectrans.v.beautified vectrans.required_vo: vectrans.v vecop.vo
vectrans.vio: vectrans.v vecop.vio
vectrans.vos vectrans.vok vectrans.required_vos: vectrans.v vecop.vos
VASStoVAS.vo VASStoVAS.glob VASStoVAS.v.beautified VASStoVAS.required_vo: VASStoVAS.v vecop.vo vectrans.vo monad.vo
VASStoVAS.vio: VASStoVAS.v vecop.vio vectrans.vio monad.vio
VASStoVAS.vos VASStoVAS.vok VASStoVAS.required_vos: VASStoVAS.v vecop.vos vectrans.vos monad.vos
