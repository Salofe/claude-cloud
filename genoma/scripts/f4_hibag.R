# Fase 4: imputación HLA con HIBAG (modelos InfiniumGlobal, hg19) usando genotipos medidos 23andMe.
# Codifica dosis del alelo A del modelo; usa el complemento solo si no es palindrómico.
suppressMessages(library(HIBAG))
args <- commandArgs(TRUE)
geno_file <- args[1]; model_file <- args[2]; out <- args[3]
g <- read.table(geno_file, sep="\t", comment.char="#", header=FALSE, colClasses="character", col.names=c("rs","chr","pos","gt"))
g <- g[g$chr=="6" & g$gt!="--" & grepl("^[ACGT]+$", g$gt), ]
gm <- setNames(g$gt, g$pos)
comp <- c(A="T",C="G",G="C",T="A")
mobj <- get(load(model_file))
res <- list()
for (locus in names(mobj)) {
  m <- hlaModelFromObj(mobj[[locus]])
  al <- strsplit(m$snp.allele, "/")
  pos <- as.character(m$snp.position)
  dose <- rep(NA_integer_, length(pos)); nflip <- 0; ndirect <- 0
  for (i in seq_along(pos)) {
    x <- gm[pos[i]]; if (is.na(x)) next
    A <- al[[i]][1]; B <- al[[i]][2]; l <- strsplit(x, "")[[1]]
    if (all(l %in% c(A,B))) { dose[i] <- sum(l==A); ndirect <- ndirect+1 }
    else if (!(paste(sort(c(A,B)),collapse="") %in% c("AT","CG")) && all(comp[l] %in% c(A,B))) { dose[i] <- sum(comp[l]==A); nflip <- nflip+1 }
  }
  geno <- hlaMakeSNPGeno(matrix(dose, ncol=1), sample.id="SANTIAGO", snp.id=m$snp.id, snp.position=m$snp.position,
                         A.allele=sapply(al,`[`,1), B.allele=sapply(al,`[`,2), assembly="hg19")
  p <- predict(m, geno, type="response+prob", match.type="Position", verbose=FALSE)
  v <- p$value
  # top-3 alternativas
  pr <- p$postprob[,1]; o <- order(pr, decreasing=TRUE)[1:3]
  alt <- paste(sprintf("%s(%.2f)", rownames(p$postprob)[o], pr[o]), collapse="; ")
  res[[locus]] <- data.frame(locus=locus, allele1=v$allele1, allele2=v$allele2, prob=round(v$prob,3), matching=round(v$matching,3),
                             snps_modelo=length(pos), snps_usados=sum(!is.na(dose)), directos=ndirect, flip=nflip, top3=alt)
  hlaClose(m)
}
r <- do.call(rbind, res); print(r[,1:9]); write.table(r, out, sep="\t", quote=FALSE, row.names=FALSE)
