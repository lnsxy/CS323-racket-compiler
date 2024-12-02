(let ([x
       (let ([y 1]) (+ y 2))])
  (+ (let ([z 2]) z)
     (let ([k 3]) k)))